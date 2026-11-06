-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_expHorner_eq_e
-- name    : OAI.SharpPlanar.IntegerIntervals.expHorner_eq_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:51:48.714483+00:00
-- url     : https://prove2.me/theorems/9f61a0fc-399a-43ea-be6b-1bae15b2aa3f
-- title:
--   OAI.SharpPlanar.IntegerIntervals.expHorner_eq_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.expHorner_eq` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma expHorner_eq_e (z : ℂ) (k n : ℕ) :
--       expHorner z k n = ∑ i ∈ Finset.range (n+1), z^i/((k+i).factorial:ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.expHorner` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerIntervals.exp_small_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.expHorner_eq)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma expHorner_eq_e (z : ℂ) (k n : ℕ) :
    expHorner z k n = ∑ i ∈ Finset.range (n+1), z^i/((k+i).factorial:ℂ) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
