-- Prove2me | Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_21_0_90
-- name    : OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:51:22.427176+00:00
-- url     : https://prove2.me/theorems/65d9fdd8-5225-4bb4-bfc9-def80b7a20ae
-- title:
--   OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90` of [lean/OAI/Geometry/Convex/GeneralMahler/Middle/Rfalse21.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Middle/Rfalse21.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.SCal.Mid.Tab`, with `open Grid Cert Cert.IV`):
--
--   ```lean
--   lemma cfalse_21_0_90 : By (tile Cn false 21) 0 90
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.SCal.Grid.By` (definitions bundle `OAIQ026G001` of this split); `OAI.GeneralMahler.SCal.Mid.tile` and `OAI.GeneralMahler.SCal.Mid.Tab.Cn` (definitions bundle `OAIQ026G002` of this split).
--
--   **Used by.** The proof of `OAI.GeneralMahler.SCal.Mid.Tab.gfalse` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Middle/Rfalse21.lean (declaration OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90)

import Mathlib
import Definitions.Def_OAIQ026G002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_21_0_90 : By (tile Cn false 21) 0 90 := by
  sorry
end GeneralMahler.SCal.Mid.Tab

end OAI
end
