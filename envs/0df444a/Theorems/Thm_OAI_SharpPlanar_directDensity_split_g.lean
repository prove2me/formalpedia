-- Prove2me | Theorems.Thm_OAI_SharpPlanar_directDensity_split_g
-- name    : OAI.SharpPlanar.directDensity_split_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T19:20:55.276636+00:00
-- url     : https://prove2.me/theorems/ea365686-ae97-4939-a299-1f4599fe22bd
-- title:
--   OAI.SharpPlanar.directDensity_split_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.directDensity_split` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open Set Filter MeasureTheory Asymptotics`, `open scoped Topology ContDiff SchwartzMap`, `open scoped SchwartzMap`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma directDensity_split_g (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
--       (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel ell s t) =
--         (p.c₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, u 0 j t * directKernel ell s t) +
--         (p.d₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, v 0 j t * directKernel ell s t) +
--         (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t * directKernel ell s t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.CardinalData`, `OAI.SharpPlanar.density`, `OAI.SharpPlanar.positiveData`, `OAI.SharpPlanar.u` and `OAI.SharpPlanar.v` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.directKernel` (definitions bundle `OAIQ098G1643` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.directDensity_series_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.directDensity_split)

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

open MeasureTheory
open scoped ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

namespace SharpPlanar
open MeasureTheory Set

lemma directDensity_split_g (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel ell s t) =
      (p.c₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, u 0 j t * directKernel ell s t) +
      (p.d₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, v 0 j t * directKernel ell s t) +
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t * directKernel ell s t) := by
  sorry

end SharpPlanar

end OAI
end
