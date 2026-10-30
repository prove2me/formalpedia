-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_exponent_bounds
-- name    : NestedLogitAssort.DeltaGrid.exponent_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:41.824966+00:00
-- url     : https://prove2.me/theorems/3d1b6f49-5736-4026-8193-74ba503ca546
-- title:
--   Proof of Theorem 12: the exponent bounds $\delta^{\bar\gamma}\delta^{-[\gamma_i-1]^+}\delta^{-[1-\gamma_i]^+}\ge1$ and $\delta^{\bar\gamma+\gamma_i+1}\le\delta^{2\bar\gamma+1}$
-- statement:
--   Let $\delta>1$, and let $\gamma$ and $\bar\gamma$ be real numbers with $0\le\gamma\le\bar\gamma$ and $\bar\gamma>1$. Then
--
--   $$
--   \delta^{\bar\gamma}\,\delta^{-[\gamma-1]^+}\,\delta^{-[1-\gamma]^+}\ge1\qquad\text{and}\qquad\delta^{\bar\gamma+\gamma+1}\le\delta^{2\bar\gamma+1},
--   $$
--
--   where $[a]^+=\max\{a,0\}$. In the proof of Theorem 12, $\gamma=\gamma_i$ and $\bar\gamma=\max_{i\in M}\gamma_i$; this is where the standing assumption $\bar\gamma>1$ of Section 6 enters.
--
--   Differences from the source:
--   - generalization: γ = γ_i ≥ 0 and γ̄ = max_{i∈M} γ_i > 1 → any reals γ, γ̄ with 0 ≤ γ ≤ γ̄ and γ̄ > 1; reason: γ_i ≤ max_i γ_i is the only property of the maximum the step uses; the statement specializes to the page
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54

import Mathlib

namespace NestedLogitAssort.DeltaGrid

/-- **The exponent bounds `δ^{γ̄} δ^{−[γ_i−1]^+} δ^{−[1−γ_i]^+} ≥ 1` and `δ^{γ̄+γ_i+1} ≤ δ^{2γ̄+1}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54 (unnumbered): "If we have `γ_i ≤ 1`, then
`γ̄ − [γ_i − 1]^+ − [1 − γ_i]^+ = γ̄ − 1 + γ_i ≥ 0`, where we use the fact that `γ̄ > 1`. On the
other hand, if we have `γ_i > 1`, then `γ̄ − [γ_i − 1]^+ − [1 − γ_i]^+ = γ̄ − γ_i + 1 ≥ 0` since
`γ̄ ≥ γ_i`. Therefore, `δ^{γ̄} δ^{−[γ_i−1]^+} δ^{−[1−γ_i]^+} ≥ 1`. We also have
`δ^{γ̄+γ_i+1} ≤ δ^{2γ̄+1}`."

For `δ > 1`, `0 ≤ γ ≤ γ̄` and `γ̄ > 1` (the standing assumption of Section 6, p. 25).

**Formalization Note.** All powers are `Real.rpow`; `[a]^+` is `max a 0`. -/
theorem exponent_bounds (δ : ℝ) (hδ : 1 < δ) (γ γbar : ℝ) (hγ : 0 ≤ γ) (hγle : γ ≤ γbar)
    (hγbar : 1 < γbar) :
    1 ≤ δ ^ γbar * δ ^ (-(max (γ - 1) 0)) * δ ^ (-(max (1 - γ) 0)) ∧
      δ ^ (γbar + γ + 1) ≤ δ ^ (2 * γbar + 1) := by sorry

end NestedLogitAssort.DeltaGrid
