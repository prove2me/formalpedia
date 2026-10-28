-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_polygon_full_low_homology_finite
-- name    : OAI.SimpleAmenable.polygon_full_low_homology_finite
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-28T01:26:06.359106+00:00
-- url     : https://prove2.me/theorems/90629540-85cd-43b9-ad18-e386601c7830
-- title:
--   OAI.SimpleAmenable.polygon_full_low_homology_finite: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.polygon_full_low_homology_finite` of [lean/OAI/GroupTheory/SimpleAmenable/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open IntervalBar.Diagram`):
--
--   ```lean
--   lemma polygon_full_low_homology_finite (a m:ℕ) (ha:0<a) (hm : 34 ≤ m) :
--       Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ∧
--       Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.main` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Main.lean (declaration OAI.SimpleAmenable.polygon_full_low_homology_finite)

import Mathlib
import Definitions.Def_OAIQ65Sa001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable
open IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2

lemma polygon_full_low_homology_finite (a m:ℕ) (ha:0<a) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ∧
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) := by
  sorry

end SimpleAmenable

end

end OAI
end
