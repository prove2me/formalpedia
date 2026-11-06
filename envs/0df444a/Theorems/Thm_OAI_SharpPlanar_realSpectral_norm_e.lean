-- Prove2me | Theorems.Thm_OAI_SharpPlanar_realSpectral_norm_e
-- name    : OAI.SharpPlanar.realSpectral_norm_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:43:26.690508+00:00
-- url     : https://prove2.me/theorems/a59ecd47-e7ae-4f03-941a-98e4f6c212f1
-- title:
--   OAI.SharpPlanar.realSpectral_norm_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.realSpectral_norm` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma realSpectral_norm_e (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
--       ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.directDensity_tsum_e`, `OAI.SharpPlanar.direct_basis_integral_bound_e`, `OAI.SharpPlanar.error_large_cap_e`, `OAI.SharpPlanar.error_one_cap_e`, `OAI.SharpPlanar.error_two_cap_e`, `OAI.SharpPlanar.error_zero_cap_e`, `OAI.SharpPlanar.exactLeft_origin_positive_e`, `OAI.SharpPlanar.exact_sign_tail_e`, `OAI.SharpPlanar.halfSign_0_N1_right_e`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_e` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.realSpectral_norm)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

open MeasureTheory
open scoped ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

lemma realSpectral_norm_e (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
    ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell := by
  sorry

end SharpPlanar

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

end OAI
end
