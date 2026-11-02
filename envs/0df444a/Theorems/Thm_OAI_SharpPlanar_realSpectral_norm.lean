-- Prove2me | Theorems.Thm_OAI_SharpPlanar_realSpectral_norm
-- name    : OAI.SharpPlanar.realSpectral_norm
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T14:22:06.163491+00:00
-- url     : https://prove2.me/theorems/e7eccfaa-e48e-4c6a-b686-fdf000d57d41
-- title:
--   OAI.SharpPlanar.realSpectral_norm: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.realSpectral_norm` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma realSpectral_norm (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
--       ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.analytic_zero`, `OAI.SharpPlanar.directDensity_tsum`, `OAI.SharpPlanar.direct_basis_integral_bound`, `OAI.SharpPlanar.error_large_cap`, `OAI.SharpPlanar.error_zero_cap`, `OAI.SharpPlanar.exactJet_jets_two`, `OAI.SharpPlanar.exactJet_node_zero`, `OAI.SharpPlanar.exactLeft_origin_positive`, `OAI.SharpPlanar.halfGap_nonneg_Y`, `OAI.SharpPlanar.halfSign_1_N0_right`, `OAI.SharpPlanar.halfSign_1_N1_left`, `OAI.SharpPlanar.halfSign_1_N1_right`, `OAI.SharpPlanar.normalizedCandidate_fourier_origin`, `OAI.SharpPlanar.tailErrorJet_bound`, `OAI.SharpPlanar.tailErrorJet_node` and `OAI.sharp_fourier_certificate` of this split import it.
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

lemma realSpectral_norm (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
    ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell := by
  sorry

end SharpPlanar

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

end OAI
end
