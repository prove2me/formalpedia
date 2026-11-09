-- Prove2me | Theorems.Thm_MetricTesting_Characterization_packing_distance_bound
-- name    : MetricTesting.Characterization.packing_distance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:34.339339+00:00
-- url     : https://prove2.me/theorems/22f23575-07ea-4797-991b-08a51c0c0b99
-- title:
--   Lemma 3.7 — Packing forces repair distance
-- statement:
--   Fix the standing local matrix framework with nonempty valid targets. For every array $D$ of order $n\ge k$, the minimum normalized repair distance and maximum edge-disjoint violation packing satisfy
--   $$d(D,\mathcal P_n)\ge\frac{2\nu(D)}{n^2}.$$
--   Consequently, the order-uniform packing and removal moduli satisfy
--   $$\Delta(\alpha)\ge\rho(\alpha)\qquad(\alpha>0).$$
--   Both conclusions are included. The packing threshold is $\alpha n^2$, with no factor of one half. This comparison relates edge-disjoint local obstructions to repair cost and to the global density moduli.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: infima over violation densities and minima over valid repairs → ENNReal infima with empty infimum +infinity, and attained minima of natural discrepancy counts; reason: the nonempty valid targets make the finite range of discrepancy counts attain its least element; empty far-input and packing classes retain the source convention
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 11, Lemma 3.7 (PDF p. 12)

import Definitions.Def_MetricTesting_Characterization_moduli

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Lemma 3.7, printed p.11 / PDF p.12; both clauses. -/
theorem packing_distance_bound (F : LocalData) (hP : TargetsNonempty F) :
    (∀ (n : ℕ), F.k ≤ n → ∀ D : Array F.values n,
      2 * (packingNumber F D : ℝ) / (n : ℝ)^2 ≤ repairDistance F D) ∧
    (∀ α : ℝ, 0 < α → removalModulus F α ≤ packingModulus F α) := by sorry

end MetricTesting.Characterization
