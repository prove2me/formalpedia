-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m03
-- name    : NahmiasPerishable.Inventory.m03
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:31.307804+00:00
-- url     : https://prove2.me/theorems/d5a833b1-02d5-4641-86db-981180b99f14
-- title:
--   Van Zyl differentiability and sensitivity as printed
-- statement:
--   He showed that the optimal order policy when n planning periods remain, say yₙ(x), is a continuously differentiable function of the state variable x and that −1 < yₙ′(x) ≤ 0.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: an optimal policy → existence of a family of actual Bellman minimizers; reason: ties are resolved by the existential selector, without assuming uniqueness or supplying the desired regularity as a hypothesis
--   - encoding: continuously differentiable policy on feasible stocks → ContDiffOn and explicit derivatives within [0,∞); reason: the right derivative is used at zero; the printed strict lower bound is retained, including the one-period case in insight I1
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(i), Van Zyl differentiability and sensitivity as printed (unnumbered), p. 683 (PDF 4), DOI:10.1287/opre.30.4.680; review attribution: Van Zyl [1964].

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m03 (D : Demand) (c p alpha : ℝ) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (linearModel 1 D false .fries .zero c 0 p 0 alpha).control.defined
      {x | canonical false x}) :
    ∃ q : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (q n) (Ici 0)) ∧
      (∀ n x, 0 ≤ x →
        (linearModel 1 D false .fries .zero c 0 p 0 alpha).control.optimal n
          ((fun _ => x),0) (q n x)) ∧
      (∀ n x, 0 ≤ x → ∃ v : ℝ,
        HasDerivWithinAt (q n) v (Ici 0) x ∧ -1 < v ∧ v ≤ 0) := by sorry

end NahmiasPerishable.Inventory
