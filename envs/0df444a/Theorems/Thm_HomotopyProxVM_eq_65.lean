-- Prove2me | Theorems.Thm_HomotopyProxVM_eq_65
-- name    : HomotopyProxVM.eq_65
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:31.932496+00:00
-- url     : https://prove2.me/theorems/d02708b0-612a-4c8f-83aa-dbec8ed32ce2
-- title:
--   (65), p.27 — $\sigma$ of (18) lies in $(\omega,1)$ and satisfies (65)
-- statement:
--   Let $\tau_0\in(0,1)$, $\omega\in(0,1)$, $a>0$ and $b>0$, and let $\sigma$ be given by (18) with $\Gamma=a/(\omega b)$. Then $\omega<\sigma<1$ and
--
--   $$
--   \frac{(1-\tau_0)(1-\sigma)}{\tau_0}=\frac{(\sigma-\omega)\,a}{\omega\, b} .
--   $$
--
--   In the paper $a=\|\nabla f(x^0)+\xi^0\|_2$ and $b=L_g+\|\xi^0\|_2$. This identity is the choice of the rate: it makes the error budget in (62) close with equality.
--
--   Differences from the source:
--   - generalization: a = ‖∇f(x⁰)+ξ⁰‖₂, b = L_g+‖ξ⁰‖₂ → arbitrary positive reals a, b; reason: the claim is pure algebra, and (65) is the instance at those two norms
--   - reading: C₁ > 0 and σ ∈ (ω,1), as used just before (65) → the hypotheses 0 < a, 0 < ω, 0 < b; reason: (18) is undefined at ω = 0 or b = 0, and at a = 0 one has σ = 1, the case handled in theorem_4
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Appendix B.1, (65), p.27; (18), p.8

import Mathlib
import Definitions.Def_HomotopyProxVM_sigmaConst

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Appendix B.1, (65) and (18), p.27: for `τ₀ ∈ (0,1)`, `ω ∈ (0,1)`,
`a = ‖∇f(x⁰) + ξ⁰‖₂ > 0` and `b = L_g + ‖ξ⁰‖₂ > 0`, the rate `σ` of (18) lies in `(ω, 1)` and
satisfies (65), `(1 − τ₀)(1 − σ)/τ₀ = (σ − ω) a / (ω b)`.

**Formalization Note.** A statement about real numbers: `a` and `b` stand for the two norms. The
case `a = 0`, where `σ = 1`, is outside this item and is handled in `theorem_4`. -/
theorem eq_65 {τ₀ ω a b : ℝ} (hτ₀ : τ₀ ∈ Set.Ioo (0 : ℝ) 1) (hω : ω ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    let σ := sigmaConst τ₀ ω a b
    ω < σ ∧ σ < 1 ∧ (1 - τ₀) * (1 - σ) / τ₀ = (σ - ω) * a / (ω * b) := by sorry

end HomotopyProxVM
