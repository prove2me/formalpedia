-- Prove2me | Theorems.Thm_OAI_SharpPlanar_interval_integral_tsum_uniform_e
-- name    : OAI.SharpPlanar.interval_integral_tsum_uniform_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:43:00.400304+00:00
-- url     : https://prove2.me/theorems/68ff962d-46f7-4bfd-a259-6d8460d4dcdd
-- title:
--   OAI.SharpPlanar.interval_integral_tsum_uniform_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.interval_integral_tsum_uniform` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma interval_integral_tsum_uniform_e {ι : Type*} [Countable ι]
--       {f : ι → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
--       (hf : ∀ i, ContinuousOn (f i) (Icc a b))
--       (g : ι → ℝ) (hg : Summable g)
--       (hbound : ∀ i t, t ∈ Icc a b → ‖f i t‖ ≤ g i) :
--       (∫ t in a..b, ∑' i, f i t) = ∑' i, ∫ t in a..b, f i t
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.directDensity_tsum_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.interval_integral_tsum_uniform)

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

lemma interval_integral_tsum_uniform_e {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, ContinuousOn (f i) (Icc a b))
    (g : ι → ℝ) (hg : Summable g)
    (hbound : ∀ i t, t ∈ Icc a b → ‖f i t‖ ≤ g i) :
    (∫ t in a..b, ∑' i, f i t) = ∑' i, ∫ t in a..b, f i t := by
  sorry

end SharpPlanar

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

end OAI
end
