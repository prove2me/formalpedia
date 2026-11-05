-- Prove2me | Theorems.Thm_OAI_SharpPlanar_expCut_smooth_e
-- name    : OAI.SharpPlanar.expCut_smooth_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:44:23.276877+00:00
-- url     : https://prove2.me/theorems/f81ca167-baa2-49fc-8475-8085aa7d7f76
-- title:
--   OAI.SharpPlanar.expCut_smooth_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.expCut_smooth` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open Set Filter MeasureTheory Asymptotics`, `open scoped Topology ContDiff SchwartzMap`):
--
--   ```lean
--   lemma expCut_smooth_e (c : ℝ) : ContDiff ℝ ∞ (expCut c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.expCut` (definitions bundle `OAIQ098E012` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.expCut_decay_e` and the definitions bundle `OAIQ098E239` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.expCut_smooth)

import Mathlib
import Definitions.Def_OAIQ098E012

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

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

lemma expCut_smooth_e (c : ℝ) : ContDiff ℝ ∞ (expCut c) := by
  sorry

end SharpPlanar

open scoped SchwartzMap

end OAI
end
