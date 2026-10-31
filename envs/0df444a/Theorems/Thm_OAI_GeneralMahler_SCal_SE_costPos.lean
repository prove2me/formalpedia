-- Prove2me | Theorems.Thm_OAI_GeneralMahler_SCal_SE_costPos
-- name    : OAI.GeneralMahler.SCal.SE.costPos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:57:44.264056+00:00
-- url     : https://prove2.me/theorems/ead6ad0f-f76c-4282-b8e0-a38bb16fa759
-- title:
--   OAI.GeneralMahler.SCal.SE.costPos: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.SCal.SE.costPos` of [lean/OAI/Geometry/Convex/GeneralMahler/Segment/Positive.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Segment/Positive.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.SCal.SE`, with `open Set Filter Real MeasureTheory`, `open Tag Grid Profile Jet Segment`):
--
--   ```lean
--   lemma costPos (H:NG)(m h:ℝ)(hm:14/10≤left m h)(hh:16/100 ≤h):
--       costs (seg m h)<(1+tmax)*fstar h
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.tmax` (definitions bundle `OAIQ026G000` of this split); `OAI.GeneralMahler.SCal.SE.left` (definitions bundle `OAIQ026G001` of this split); `OAI.GeneralMahler.SCal.NG`, `OAI.GeneralMahler.SCal.SE.costs`, `OAI.GeneralMahler.SCal.SE.fstar` and `OAI.GeneralMahler.SCal.SE.seg` (definitions bundle `OAIQ026G002` of this split).
--
--   **Used by.** The proof of `OAI.GeneralMahler.SCal.Eq04full` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Segment/Positive.lean (declaration OAI.GeneralMahler.SCal.SE.costPos)

import Mathlib
import Definitions.Def_OAIQ026G002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Real MeasureTheory
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable (H:NG)(m:ℝ){h:ℝ}

lemma costPos (H:NG)(m h:ℝ)(hm:14/10≤left m h)(hh:16/100 ≤h):
    costs (seg m h)<(1+tmax)*fstar h:= by
  sorry
end GeneralMahler.SCal.SE

end

end OAI
end
