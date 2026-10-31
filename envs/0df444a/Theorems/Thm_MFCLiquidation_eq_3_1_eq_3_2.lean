-- Prove2me | Theorems.Thm_MFCLiquidation_eq_3_1_eq_3_2
-- name    : MFCLiquidation.eq_3_1_eq_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:26.618655+00:00
-- url     : https://prove2.me/theorems/0ef2434b-868d-44e4-a2d2-4c320a59cbfd
-- title:
--   (3.1)–(3.2): (2.15) as a matrix Riccati equation and its $\tilde\Lambda$-shift (corrected: terminal matrix $\operatorname{diag}(\gamma_2/2,0)$)
-- statement:
--   Assume the standing assumption and $\gamma_2>0$, and let $T\in\mathbb R$. For functions $B_{11},B_{13},B_{33}$ put $\mathcal P_t=\begin{pmatrix}B_{11,t}&B_{13,t}\\B_{13,t}&B_{33,t}\end{pmatrix}$. Then:
--
--   1. $(B_{11},B_{13},B_{33})$ solves (2.15) on $[0,T]$ if and only if $\mathcal P$ solves (3.1),
--   $$\dot{\mathcal P}_t=\mathcal P_t\mathcal N_2\mathcal N_0\mathcal N_2^\top\mathcal P_t+\mathcal N_1\mathcal P_t+\mathcal P_t\mathcal N_1^\top-\mathcal M,\qquad \mathcal P_T=\operatorname{diag}(\gamma_2/2,0);$$
--   2. for every $\Lambda\in\mathbb R$, $\mathcal P$ solves (3.1) if and only if $\tilde{\mathcal P}=\mathcal P+\tilde\Lambda$ solves (3.2),
--   $$\dot{\tilde{\mathcal P}}_t=\tilde{\mathcal P}_t\mathcal N_2\mathcal N_0\mathcal N_2^\top\tilde{\mathcal P}_t+\tilde{\mathcal N}_1\tilde{\mathcal P}_t+\tilde{\mathcal P}_t\tilde{\mathcal N}_1^\top-\tilde{\mathcal M},\qquad \tilde{\mathcal P}_T=\operatorname{diag}(\gamma_2/2,0)+\tilde\Lambda .$$
--
--   The shift by $\tilde\Lambda$ turns the Riccati equation, whose constant term $-\mathcal M$ is not of the standard sign, into one to which the standard theory applies once $\tilde{\mathcal M}\succeq0$.
--
--   Differences from the source:
--   - correction: terminal matrix 𝒢 = [[γ₂, 0], [0, 0]] in (3.1) (p.12) → terminal matrix diag(γ₂/2, 0) (Params.termMat); reason: (2.15) has B₁₁,T = γ₂/2, so with the printed 𝒢 the claimed equivalence of (2.15) and (3.1) fails for every solution (the terminal values differ by γ₂/2 ≠ 0); the terminal value on p.15 is γ₂/2 + Λα², which confirms the γ₂/2
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
--   - generalization: (3.1) and (3.2) on [0, T] with T > 0, and the claim that 𝒫̃ satisfies (3.2) when 𝒫 satisfies (3.1) → any real T, and an equivalence for every Λ ∈ ℝ; reason: taking T > 0 and the forward direction gives the page; the converse is what the page uses when it says that it is enough to solve (3.2)
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (3.1) and (3.2) with 𝒫, 𝒩₁, 𝒩₂, 𝒩₀, ℳ, 𝒢, Λ̃, 𝒩̃₁, ℳ̃, p.12

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Matrix

namespace MFCLiquidation

/-- (3.1) and (3.2), arXiv:2207.00446v3, p.12: the system (2.15) is the matrix Riccati equation
(3.1) for `𝒫 = [[B₁₁, B₁₃], [B₁₃, B₃₃]]`, and for every `Λ`, `𝒫` solves (3.1) if and only if
`𝒫̃ = 𝒫 + Λ̃` solves (3.2). The terminal matrix is `diag(γ₂/2, 0)`, correcting the `γ₂` printed on
p.12 (`Params.termMat`). -/
theorem eq_3_1_eq_3_2 (p : Params) (hp : p.Standing) (hγ : 0 < p.γ₂) (T : ℝ)
    (B₁₁ B₁₃ B₃₃ : ℝ → ℝ) :
    let P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => !![B₁₁ s, B₁₃ s; B₁₃ s, B₃₃ s]
    (p.SolvesB T B₁₁ B₁₃ B₃₃ ↔ IsMatRiccati p.S p.N₁ p.M p.termMat T P) ∧
    ∀ Λ : ℝ, IsMatRiccati p.S p.N₁ p.M p.termMat T P ↔
      IsMatRiccati p.S (p.N₁Tilde Λ) (p.MTilde Λ) (p.termMat + p.lamTilde Λ) T
        (fun s => P s + p.lamTilde Λ) := by sorry

end MFCLiquidation
