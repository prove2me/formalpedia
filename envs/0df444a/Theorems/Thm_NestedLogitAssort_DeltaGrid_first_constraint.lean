-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_first_constraint
-- name    : NestedLogitAssort.DeltaGrid.first_constraint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:28.38082+00:00
-- url     : https://prove2.me/theorems/09820015-be58-416c-b831-a8df3c7b390f
-- title:
--   Proof of Theorem 12: the scaled solution satisfies the first constraint of (3)
-- statement:
--   Let $v_0\ge0$ be the weight of choosing no nest, $\delta>1$, $\bar\gamma\ge0$ and $x\ge0$, and let $(y_i)_{i\in M}$ satisfy the first constraint of (4), $v_0x\ge\sum_{i\in M}y_i$. Then
--
--   $$
--   v_0\,\delta^{2\bar\gamma+1}x\ge\sum_{i\in M}\delta^{\bar\gamma+1}y_i ,
--   $$
--
--   so the scaled point $(\delta^{2\bar\gamma+1}x,\delta^{\bar\gamma+1}y)$ satisfies the first constraint of (3). In the proof of Theorem 12, $(x,y)=(\hat x,\hat y)$ and $\bar\gamma=\max_i\gamma_i>1$.
--
--   Differences from the source:
--   - reading: v0 is a preference weight (p. 7 allows v0 = 0) → hypothesis 0 ≤ v0; reason: preference weights of a logit model are nonnegative
--   - generalization: (x̂, ŷ), the optimal solution of (4), and γ̄ = max_i γ_i > 1 → any x ≥ 0 and y with ∑_i y_i ≤ v0 x, any γ̄ ≥ 0; reason: x̂ ≥ 0 by xhat_nonneg and (x̂, ŷ) satisfies the first constraint of (4); the statement specializes to the page
--   - encoding: δ^(γ̄+1), δ^(2γ̄+1) → Real.rpow with real exponents; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Instance

namespace NestedLogitAssort.DeltaGrid

/-- **The scaled solution satisfies the first constraint of (3).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54 (unnumbered): "we have
`v_0 x̂ ≥ ∑_{i∈M} ŷ_i`. This implies that `v_0 δ^{2γ̄+1} x̂ ≥ v_0 δ^{γ̄+1} x̂ ≥ ∑_{i∈M} δ^{γ̄+1} ŷ_i`".

For `v_0 ≥ 0`, `γ̄ ≥ 0`, `δ > 1`, `x ≥ 0` and any `y` with `∑_i y_i ≤ v_0 x`:
`∑_i δ^{γ̄+1} y_i ≤ v_0 (δ^{2γ̄+1} x)`.

**Formalization Note.** The page has `(x, y) = (x̂, ŷ)` and `γ̄ = max_i γ_i > 1`. Powers are
`Real.rpow`. -/
theorem first_constraint {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (γbar : ℝ) (hγbar0 : 0 ≤ γbar) (δ : ℝ) (hδ : 1 < δ)
    (x : ℝ) (hx : 0 ≤ x) (y : M → ℝ) (hy : ∑ i, y i ≤ I.v0 * x) :
    ∑ i, δ ^ (γbar + 1) * y i ≤ I.v0 * (δ ^ (2 * γbar + 1) * x) := by sorry

end NestedLogitAssort.DeltaGrid
