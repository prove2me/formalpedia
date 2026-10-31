-- Prove2me | Theorems.Thm_MFCLiquidation_completion_of_squares
-- name    : MFCLiquidation.completion_of_squares
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:18.43333+00:00
-- url     : https://prove2.me/theorems/1e1d4294-8b1a-421a-9060-e4270429463f
-- title:
--   p.20: the four completion-of-squares identities from (A.15)–(A.18) (corrected: $B_{13}$ coefficient $2\alpha\gamma_2$ in (2.16))
-- statement:
--   Assume the standing assumption and $\gamma_2>0$. Let $A,B,D$ be built from arbitrary values $(a_{11},a_{13},a_{33})$, $(b_{11},b_{13},b_{33})$, $(d_1,d_3)$ by the relations of p.9, let $\dot A,\dot B,\dot D$ be given by the right sides of (2.14), (2.15) and (2.16), and let $\dot F=-g$ with $g$ the driver of (2.17) at volatility $\sigma$. Then, with $\mathcal D=(0,\sigma,0)^\top$,
--   $$\frac{(I^A)^\top I^A}{\tilde a}=\mathcal Q+\mathcal H^\top A+A\mathcal H+\dot A,\qquad \frac{(I^B)^\top I^B}{a}=\mathcal Q+\dot B+\mathcal H^\top B+B\mathcal H+\overline{\mathcal H}^\top B+B\overline{\mathcal H},$$
--   $$\frac{2I^DI^B}{a}=2\mathcal G^\top B+\dot D^\top+D^\top\mathcal H+D^\top\overline{\mathcal H},\qquad \frac{(I^D)^2}{a}=\mathcal D^\top A\mathcal D+D^\top\mathcal G+\dot F .$$
--
--   Along the solutions of (2.14)–(2.17) these identities turn the expanded cost into the two squares of Proposition 4.1.
--
--   Differences from the source:
--   - correction: (2.16), first line of Ḋ₁, second bracket: −2λγ₂ + 2(γ₁α − γ₂ρ)B₁₁ + γ₁γ₂α + αγ₂B₁₃ → the same bracket with 2αγ₂B₁₃ (the first bracket X₁ of (2.15)); reason: with the printed αγ₂B₁₃ the identity 2I^DI^B/a = 2𝒢ᵀB + Ḋᵀ + Dᵀℋ + Dᵀℋ̄ used in the proof of Proposition 4.1 (p.20) leaves the residual αB₁₃(−αγ₁D₁ + γ₂ρD₁ − αγ₂D₃ + αγ₁γ₂E[x₀])/(2γ₂(αγ₁ − γ₂ρ − λ)) ≠ 0; counterexample with the Fig. 2 parameters (ρ = 0.4, γ₁ = 0.1, γ₂ = 0.5, α = 1.8, β = 3, λ = 0, E[x₀] = 1, T = 1, all assumptions hold): printed D(0) = (0.2248, 0.0436), corrected D(0) = (0.0983, 0.0475), so the printed (2.20) is false for one of two initial states differing only in E[C_{t−}]
--   - generalization: the identities along the solutions A_s, B_s, D_s, F_s → the identities at every point of the coefficient space, with the derivatives replaced by the right sides of (2.14)–(2.17); reason: along a solution the derivatives equal the right sides, so the pointwise identities specialize to the paper's
--   - encoding: Ḟ → −g, the negative of the driver of (2.17); reason: (2.17) reads −dF = g dt − Z^F dW; the identity concerns the drift of F
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, proof of Proposition 4.1, p.20: "By (A.15), (A.16), (A.17) and (A.18) in the appendix it holds that" (four displays); 𝒬, p.19

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Matrix

namespace MFCLiquidation

/-- The four identities on p.20 of arXiv:2207.00446v3, from (A.15)–(A.18), which complete the
squares in the proof of Proposition 4.1, at any point `(a, b, d)` of the coefficient space, with
the time derivatives given by the right sides of (2.14), (2.15) and the corrected (2.16). In the
last identity `Ḟ = −g`, with `g` the generator of (2.17). -/
theorem completion_of_squares (p : Params) (hp : p.Standing) (hγ : 0 < p.γ₂)
    (Ex0 sg a₁₁ a₁₃ a₃₃ b₁₁ b₁₃ b₃₃ d₁ d₃ : ℝ) :
    let A := p.symMat a₁₁ a₁₃ a₃₃
    let B := p.symMat b₁₁ b₁₃ b₃₃
    let Adot := p.symMatDot (p.rhsA₁₁ a₁₁) (p.rhsA₁₃ a₁₁ a₁₃) (p.rhsA₃₃ a₁₃ a₃₃)
    let Bdot := p.symMatDot (p.rhsB₁₁ b₁₁ b₁₃) (p.rhsB₁₃ b₁₁ b₁₃ b₃₃) (p.rhsB₃₃ b₁₃ b₃₃)
    let Dv := p.dVec d₁ d₃
    let Ddot := p.dVec (p.rhsD₁ Ex0 b₁₁ b₁₃ d₁ d₃) (p.rhsD₃ Ex0 b₁₃ b₃₃ d₁ d₃)
    let iA := p.IA a₁₁ a₁₃
    let iB := p.IB b₁₁ b₁₃ b₃₃
    let iD := p.ID Ex0 d₁ d₃
    (1 / p.aTilde) • Matrix.vecMulVec iA iA = p.Q + p.Hᵀ * A + A * p.H + Adot ∧
    (1 / p.a) • Matrix.vecMulVec iB iB = p.Q + Bdot + p.Hᵀ * B + B * p.H + p.Hbarᵀ * B + B * p.Hbar ∧
    (2 * iD / p.a) • iB = (2 : ℝ) • (p.G Ex0 ᵥ* B) + Ddot + Dv ᵥ* p.H + Dv ᵥ* p.Hbar ∧
    iD ^ 2 / p.a = ![0, sg, 0] ⬝ᵥ (A *ᵥ ![0, sg, 0]) + Dv ⬝ᵥ p.G Ex0
      - p.genF Ex0 sg a₁₁ d₁ d₃ := by sorry

end MFCLiquidation
