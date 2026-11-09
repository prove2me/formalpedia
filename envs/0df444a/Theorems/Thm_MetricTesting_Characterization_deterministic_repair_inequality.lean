-- Prove2me | Theorems.Thm_MetricTesting_Characterization_deterministic_repair_inequality
-- name    : MetricTesting.Characterization.deterministic_repair_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:27.513535+00:00
-- url     : https://prove2.me/theorems/ba13db00-3127-4391-94d6-94ed034f4525
-- title:
--   Proposition 3.9 — Deterministic repair inequality
-- statement:
--   Fix the standing local matrix framework with nonempty valid targets. Let $D$ be any array of order $n\ge k$, let $\nu(D)$ be its maximum edge-disjoint violation packing size, and let $\Gamma$ be the uniform completion repair modulus. Then
--   $$d(D,\mathcal P_n)\le\Gamma\!\left(\frac{\binom k2\nu(D)}{n^2}\right)+\frac{2\binom k2\nu(D)}{n^2}.$$
--   The argument of $\Gamma$ is half the separately added normalized Hamming term. No extendability or measurability hypothesis is imposed. This deterministic estimate relates repair distance to the independently defined completion modulus and packing number.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: infima over violation densities and minima over valid repairs → ENNReal infima with empty infimum +infinity, and attained minima of natural discrepancy counts; reason: the nonempty valid targets make the finite range of discrepancy counts attain its least element; empty far-input and packing classes retain the source convention
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 11, Proposition 3.9 (PDF p. 12)

import Definitions.Def_MetricTesting_Characterization_moduli

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Proposition 3.9, printed p.11 / PDF p.12. The Gamma argument
has coefficient 1 and the added Hamming term coefficient 2. -/
theorem deterministic_repair_inequality (F : LocalData) (hP : TargetsNonempty F)
    (n : ℕ) (hn : F.k ≤ n) (D : Array F.values n) :
    repairDistance F D ≤
      completionModulus F ((Nat.choose F.k 2 : ℝ) * (packingNumber F D : ℝ) / (n : ℝ)^2) +
        2 * (Nat.choose F.k 2 : ℝ) * (packingNumber F D : ℝ) / (n : ℝ)^2 := by sorry

end MetricTesting.Characterization
