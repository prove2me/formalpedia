-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_horner_step_g
-- name    : OAI.SharpPlanar.IntegerIntervals.horner_step_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T09:12:50.368467+00:00
-- url     : https://prove2.me/theorems/e158e130-0567-42e2-a302-23123bdc32ea
-- title:
--   OAI.SharpPlanar.IntegerIntervals.horner_step_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.horner_step` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma horner_step_g {a b p m c : CBox} {z : ℂ} {k n : ℕ}
--       (hz : a.Contains z) (hb : b.Contains (expHorner z (k+1) n))
--       (hp : p.RatCheck 1 (k.factorial:ℤ) 0 1) (hm : a.MulCheck b m)
--       (hc : p.AddCheck m c) : c.Contains (expHorner z k (n+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.expHorner` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.AddCheck` (definitions bundle `OAIQ098G076` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains`, `OAI.SharpPlanar.IntegerIntervals.CBox.MulCheck` and `OAI.SharpPlanar.IntegerIntervals.CBox.RatCheck` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_contains_g` and `OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.horner_step)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma horner_step_g {a b p m c : CBox} {z : ℂ} {k n : ℕ}
    (hz : a.Contains z) (hb : b.Contains (expHorner z (k+1) n))
    (hp : p.RatCheck 1 (k.factorial:ℤ) 0 1) (hm : a.MulCheck b m)
    (hc : p.AddCheck m c) : c.Contains (expHorner z k (n+1)) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
