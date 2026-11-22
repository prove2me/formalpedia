-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormIndexOneTargetedV2
-- name    : Kyprianou.Ch01.stableLevyExponentFormIndexOneTargetedV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:13:06.954044+00:00
-- url     : https://prove2.me/theorems/fe181b81-eeae-4ebd-bdef-95bc1a54bace
-- title:
--   Index-one stable Lévy exponent with collision-safe targeted triplet imports
-- statement:
--   The complete source-exact index-one stable Lévy characteristic exponent representation, including the logarithmic term and the full original triplet and Fourier-parameter conditions. The mathematical statement is byte-for-byte identical after the theorem name change to the published Chapter 1 Open theorem 802ca6d6-48be-4ce7-bad9-dffd367b9cff. Only the legacy umbrella Lévy-triplet exponent import is replaced by the already published mathematically equivalent targeted Definition, to avoid an independently demonstrated source import conflict in the chapter-wide certificate bundle.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.6, index-one stable Lévy characteristic exponent; original global theorem 802ca6d6-48be-4ce7-bad9-dffd367b9cff.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableLevyExponentFormIndexOneTargetedV2
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let alpha : ℝ := 1;
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  sorry
