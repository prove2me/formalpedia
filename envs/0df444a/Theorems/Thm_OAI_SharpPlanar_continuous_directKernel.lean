-- Prove2me | Theorems.Thm_OAI_SharpPlanar_continuous_directKernel
-- name    : OAI.SharpPlanar.continuous_directKernel
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T14:22:42.85925+00:00
-- url     : https://prove2.me/theorems/043a23cc-1252-4d84-86bd-7bdf8da5f32d
-- title:
--   OAI.SharpPlanar.continuous_directKernel: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.continuous_directKernel` of [lean/OAI/Analysis/PlanarPacking/Entire.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory`, `open scoped ComplexConjugate`, `open Set Filter MeasureTheory`, `open scoped Topology FourierTransform ContDiff`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma continuous_directKernel (ell : ℕ) (s : ℝ) : Continuous (directKernel ell s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.directKernel` (definitions bundle `OAIQ098D002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.basis_piece_integrable`, `OAI.SharpPlanar.directDensity_split`, `OAI.SharpPlanar.directDensity_tsum` and `OAI.SharpPlanar.direct_piece_integrable` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean (declaration OAI.SharpPlanar.continuous_directKernel)

import Mathlib
import Definitions.Def_OAIQ098D002

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

lemma continuous_directKernel (ell : ℕ) (s : ℝ) : Continuous (directKernel ell s) := by
  sorry

end SharpPlanar

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

open scoped SchwartzMap

end OAI
end
