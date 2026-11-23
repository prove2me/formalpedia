-- Prove2me | Theorems.Thm_NoHair_nonzero_ricci_has_positive_compact_energy_test
-- name    : NoHair.nonzero_ricci_has_positive_compact_energy_test
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:56.478806+00:00
-- url     : https://prove2.me/theorems/e7cbac3b-f121-4e36-84cc-eaacb45b9ad9
-- title:
--   A nonzero Ricci tensor has strictly positive energy against a compactly supported smooth test
-- statement:
--   Choose a chart and a point where a Ricci component is nonzero. The tensor product of two copies of the inverse metric is positive definite on coordinate two-tensors, so the squared Ricci norm is strictly positive there. Multiply its Riemannian volume density by a nonnegative smooth bump supported in the chart. The resulting continuous, compactly supported density has strictly positive integral.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRicciEnergyDensity

open NoHair Set Filter Bundle MeasureTheory
open scoped ContDiff Manifold Topology

theorem NoHair.nonzero_ricci_has_positive_compact_energy_test (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (hric : ¬ RicciFlatInADMCharts Q) :
    ∃ (e : OpenPartialHomeomorph Q ADMPoint), e∈atlas ADMPoint Q ∧ ∃ χ : ADMPoint → ℝ, 0 ≤ χ ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ e.target ∧
      0 < ∫ x : ADMPoint, χ x*spatialRicciEnergyDensity (riemannianEndCoeffs e.symm) x := by sorry
