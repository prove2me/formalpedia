-- Prove2me | Theorems.Thm_HomotopyProxVM_eq_64
-- name    : HomotopyProxVM.eq_64
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:38.236222+00:00
-- url     : https://prove2.me/theorems/ef513e31-7d57-454c-8f4b-b280f3bc840e
-- title:
--   (19) ⇒ (64), p.27 — the update (19) satisfies (64) and the bounds on $1-\tau_k$
-- statement:
--   Let $\tau_0\in(0,1)$, $\omega\in(0,1)$, $a>0$, $b>0$, let $\sigma$ be given by (18), let $C_1:=\frac{(\sigma-\omega)a}{\omega b}$, and let $\tau_k$ be given by (19). Then for every $k\ge0$,
--
--   $$
--   0<\tau_k<\tau_{k+1}\le1,
--   \qquad
--   \tau_{k+1}\le\tau_k+C_1\sigma^k\tau_k\tau_{k+1},
--   \qquad
--   0<1-\tau_k\le\frac{(1-\tau_0)\sigma^k}{\tau_0} .
--   $$
--
--   This is the condition Algorithm 1 asks of the update together with the budget (64) that closes the induction in the proof of Theorem 4.
--
--   Differences from the source:
--   - generalization: a = ‖∇f(x⁰)+ξ⁰‖₂, b = L_g+‖ξ⁰‖₂, and "0 ≤ 1 − τ_k" on p.27 → arbitrary positive reals a, b, and 0 < 1 − τ_k; reason: pure algebra; the strict inequality is the one Theorem 4 claims and it implies the page's
--   - reading: C₁ > 0 and σ ∈ (ω,1), as used on p.27 → the hypotheses 0 < a, 0 < ω, 0 < b; reason: (18) is undefined at ω = 0 or b = 0; at a = 0 one has σ = 1 and τ_k is constant, the case handled in theorem_4
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Appendix B.1, (64) and the following lines, p.27

import Mathlib
import Definitions.Def_HomotopyProxVM_sigmaConst
import Definitions.Def_HomotopyProxVM_tauSeq

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Appendix B.1, (64) and the lines after (65), p.27: with
`C₁ := (σ − ω) a / (ω b)`, the update (19) satisfies `0 < τ_k < τ_{k+1} ≤ 1`, the condition (64)
`τ_{k+1} ≤ τ_k + C₁ σᵏ τ_k τ_{k+1}`, and `0 < 1 − τ_k ≤ (1 − τ₀) σᵏ / τ₀`.

**Formalization Note.** A statement about real numbers, with `a = ‖∇f(x⁰) + ξ⁰‖₂ > 0` and
`b = L_g + ‖ξ⁰‖₂ > 0`. The page prints `0 ≤ 1 − τ_k` here and `0 < 1 − τ_k` in Theorem 4; the strict
form is stated. -/
theorem eq_64 {τ₀ ω a b : ℝ} (hτ₀ : τ₀ ∈ Set.Ioo (0 : ℝ) 1) (hω : ω ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    let σ := sigmaConst τ₀ ω a b
    let C₁ := (σ - ω) * a / (ω * b)
    let τ := tauSeq τ₀ σ
    ∀ k : ℕ, 0 < τ k ∧ τ k < τ (k + 1) ∧ τ (k + 1) ≤ 1 ∧
      τ (k + 1) ≤ τ k + C₁ * σ ^ k * τ k * τ (k + 1) ∧
      0 < 1 - τ k ∧ 1 - τ k ≤ (1 - τ₀) * σ ^ k / τ₀ := by sorry

end HomotopyProxVM
