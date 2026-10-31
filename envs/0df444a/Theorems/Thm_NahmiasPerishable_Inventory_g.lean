-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_g
-- name    : NahmiasPerishable.Inventory.g
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:16.970328+00:00
-- url     : https://prove2.me/theorems/4d5e0f18-5adf-493c-bfd8-607263a31d82
-- title:
--   Convex costs and age-sensitive optimal ordering
-- statement:
--   Both authors analyzed functional equations of the form
--   Cₙ(𝐱) = minᵧ≥₀[Bₙ(𝐱, y)],
--   where
--   Bₙ(𝐱, y) = L(𝐱, y) + α ∫₀^∞ Cₙ₋₁[s(y, 𝐱, t)]f(t)dt,
--   and proved in each case that Bₙ(𝐱, y) is convex in y.
--   Let yₙ⁽ⁱ⁾(𝐱) = (∂/∂xₘ₋ᵢ)(yₙ(𝐱)). Then for n ≥ m in Fries' model and n ≥ 1 in Nahmias' model, both authors show that
--   −1 ≤ yₙ⁽¹⁾(𝐱) ≤ yₙ⁽²⁾(𝐱) ≤ ⋯ ≤ yₙ⁽ᵐ⁻¹⁾(𝐱) < 0
--   for all 𝐱 in the positive ordering region (which is again x = ∑ᵢ₌₁ᵐ⁻¹ xᵢ < x̄ when the appropriate salvage value is included).
--   Another significant result is that for x < x̄, yₙ(0) ≤ x + yₙ(𝐱) ≤ x̄ which says that after ordering, total stock will always fall between the optimal order quantity when starting inventory is zero and x̄. When x < 0, the lower bound holds with equality.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: an optimal policy → existence of a family of actual Bellman minimizers; reason: ties are resolved by the existential selector, without assuming uniqueness or supplying the desired regularity as a hypothesis
--   - reading: inverse CDF and the analogous lost-sales critical number → lower generalized quantile in EReal for backorders, and the least minimizer of the associated nonperishable salvage-adjusted objective for lost sales; reason: no positive density or uniqueness is assumed; empty and unbounded quantile sets retain their infinite endpoints
--   - encoding: age partial derivatives and the derivative ordering → oldest-first Fin k coordinates with reversed slope order and derivatives within nonnegative coordinate sections; reason: the newest age has the most negative derivative; stock added to a backlogged state first clears obligations
--   - encoding: nonperishable comparison is largest at small starting stocks → componentwise monotonicity of the reduction in orders and the comparison with (bar−x)⁺ for finite bar; reason: this expresses the printed comparison for real stock vectors; the stock bounds apply to every horizon, while only derivative bounds carry the Fries horizon restriction
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(ii), Convex costs and age-sensitive optimal ordering (unnumbered), p. 686 (PDF 7), DOI:10.1287/opre.30.4.680; review attribution: Fries [1975]; Nahmias [1975a]; Nahmias [1977a].

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open MeasureTheory Set
noncomputable section

namespace NahmiasPerishable.Inventory

theorem g (k : ℕ) (hk : 1 ≤ k) (D : Demand) (b : Bool) (a : Accounting)
    (c theta alpha : ℝ) (hc : 0 ≤ c) (htheta : 0 ≤ theta)
    (halpha : 0 < alpha ∧ alpha < 1) :
    (∀ (R : ℝ → EReal) (hR : ∀ z, 0 ≤ R z)
      (hconv : ∀ u v t : ℝ, 0 ≤ t → t ≤ 1 →
        R (t*u+(1-t)*v) ≤ (t : EReal)*R u + ((1-t : ℝ) : EReal)*R v)
      (terminal : Terminal),
      let M : FixedLife k := ⟨D,b,a,terminal,c,theta,alpha,R⟩
      M.control.defined {x | canonical b x} →
      (∀ n x, canonical b x → ConvexCost (M.control.objective n x)) ∧
      ∃ q : ℕ → AgeState k → ℝ,
        (∀ n x, canonical b x → M.control.optimal n x (q n x)) ∧
        (∀ n x, canonical b x → (a = .fries → k ≤ n) → 0 < q n x →
          ∃ slopes : Fin k → ℝ,
            (∀ i, HasDerivWithinAt (ageSection (q n) x i) (slopes i) (Ici 0) (x.1 i)) ∧
            (∀ i, -1 ≤ slopes i ∧ slopes i < 0) ∧
            (∀ i j, i ≤ j → slopes j ≤ slopes i))) ∧
    (∀ (h p : ℝ), 0 ≤ h → 0 ≤ p → 0 < p+h →
      let M := linearModel k D b a .salvage c h p theta alpha
      let bar := critical D b c h p alpha
      M.control.defined {x | canonical b x} →
      ∃ q : ℕ → AgeState k → ℝ,
        (∀ n x, canonical b x → M.control.optimal n x (q n x)) ∧
        (∀ n x, canonical b x → (0 < q n x ↔ (total x : EReal) < bar)) ∧
        (∀ n x, canonical b x → (total x : EReal) < bar →
          (q n (0,0) ≤ total x + q n x) ∧
          ((total x + q n x : ℝ) : EReal) ≤ bar ∧
          (total x < 0 → total x + q n x = q n (0,0))) ∧
        (∀ n x, canonical b x → (a = .fries → k ≤ n) → (total x : EReal) < bar →
          ∃ slopes : Fin k → ℝ,
            (∀ i, HasDerivWithinAt (ageSection (q n) x i) (slopes i) (Ici 0) (x.1 i)) ∧
            (∀ i, -1 ≤ slopes i ∧ slopes i < 0) ∧
            (∀ i j, i ≤ j → slopes j ≤ slopes i)) ∧
        (∀ (barReal : ℝ), bar = (barReal : EReal) →
          (∀ n x, canonical b x →
            q n x ≤ pos (barReal-total x)) ∧
          (∀ n (x z : Fin k → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i ≤ z i) →
            (∑ i, z i) < barReal →
            pos (barReal-total (z,0)) - q n (z,0) ≤
              pos (barReal-total (x,0)) - q n (x,0)))) := by sorry

end NahmiasPerishable.Inventory
