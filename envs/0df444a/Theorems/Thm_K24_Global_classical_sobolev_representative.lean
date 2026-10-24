-- Prove2me | Theorems.Thm_K24_Global_classical_sobolev_representative
-- name    : K24.Global.classical_sobolev_representative
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:22:44.374554+00:00
-- url     : https://prove2.me/theorems/34e91b46-5f35-4cfe-a602-83d563a4f123
-- title:
--   Quantitative classical representatives for real-order Bessel Sobolev functions
-- statement:
--   For every natural k and real r>k+2 in the original four-dimensional Sobolev model there is a finite nonnegative constant A, chosen before the input function, such that every actual real f with LocalSobolevMem r f admits a real C^k function g equal to f almost everywhere. The new representative has the same original localSobolevENN and the same original localFunctionDistribution for arbitrary valid L2 proof witnesses; every actual iterated derivative through order k is pointwise bounded by A times the original extended Sobolev norm. No continuity of f or regularity of a limit is assumed. A checked corollary proves pointwise equality and the derivative estimates for every continuous input f.
-- source:
--   Frozen K24GlobalAnalysis localSobolevENN, LocalSobolevMem and localFunctionDistribution. Local classical representative and norm-control prerequisite for SobolevConclusions.domain_banach and target_banach under original real s>4. Checked localization binding covers orders (2-j,s-j), j<=2, with original cutoff functions, cover/component weights and unrestricted finite degrees. Original source commit 8c02be189f097080feca952347c9104bfb986242.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal ContDiff

namespace K24.Global
theorem classical_sobolev_representative :
  ∀ (k : ℕ) (r : ℝ), (k : ℝ) + 2 < r → ∃ A : ℝ≥0,
    ∀ f : SobolevModel → ℝ, LocalSobolevMem r f →
    ∃ g : SobolevModel → ℝ,
      ContDiff ℝ k g ∧ f =ᵐ[volume] g ∧ LocalSobolevMem r g ∧
      localSobolevENN r g = localSobolevENN r f ∧
      (∀ (hf : MemLp (complexifyLocal f) 2 volume)
         (hg : MemLp (complexifyLocal g) 2 volume),
        localFunctionDistribution f hf = localFunctionDistribution g hg) ∧
      ∀ j ≤ k, ∀ x : SobolevModel,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖ ≤ (A : ℝ≥0∞) * localSobolevENN r f := by
  sorry
end K24.Global
