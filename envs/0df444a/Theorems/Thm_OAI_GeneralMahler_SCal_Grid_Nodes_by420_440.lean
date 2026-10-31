-- Prove2me | Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by420_440
-- name    : OAI.GeneralMahler.SCal.Grid.Nodes.by420_440
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:46:50.22409+00:00
-- url     : https://prove2.me/theorems/82777b5a-e105-4578-b648-6192cb32ce3f
-- title:
--   OAI.GeneralMahler.SCal.Grid.Nodes.by420_440: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.SCal.Grid.Nodes.by420_440` of [lean/OAI/Geometry/Convex/GeneralMahler/Scalar/Run420.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Scalar/Run420.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.SCal.Grid.Nodes`):
--
--   ```lean
--   lemma by420_440 : By passesAt 420 440
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.SCal.Grid.By` (definitions bundle `OAIQ026G001` of this split); `OAI.GeneralMahler.SCal.Grid.Nodes.passesAt` (definitions bundle `OAIQ026G002` of this split).
--
--   **Used by.** The proof of `OAI.GeneralMahler.SCal.Grid.Nodes.covered` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Scalar/Run420.lean (declaration OAI.GeneralMahler.SCal.Grid.Nodes.by420_440)

import Mathlib
import Definitions.Def_OAIQ026G002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by420_440 : By passesAt 420 440 := by
  sorry
end GeneralMahler.SCal.Grid.Nodes

end OAI
end
