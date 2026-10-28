-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_polygon_bar_homology_finite
-- name    : OAI.SimpleAmenable.polygon_bar_homology_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:27:41.142636+00:00
-- url     : https://prove2.me/theorems/8ca6c6b3-76a2-47f9-a413-16a9a764b621
-- title:
--   OAI.SimpleAmenable.polygon_bar_homology_finite: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.polygon_bar_homology_finite` of [lean/OAI/GroupTheory/SimpleAmenable/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains IntervalBar.Diagram`):
--
--   ```lean
--   lemma polygon_bar_homology_finite (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤3) :
--       Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z n:A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A`, `OAI.FreeChains.Z` and `OAI.IntervalBar.Diagram.bar` (definitions bundle `OAIQ65Sa000` of this split); `OAI.SimpleAmenable.PolygonObject`, `OAI.SimpleAmenable.PolygonObject.instGroupoid` and `OAI.SimpleAmenable.PolygonObject.monoidal` (definitions bundle `OAIQ65Sa006` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.main` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Main.lean (declaration OAI.SimpleAmenable.polygon_bar_homology_finite)

import Mathlib
import Definitions.Def_OAIQ65Sa006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable
open FreeChains IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2

lemma polygon_bar_homology_finite (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤3) :
    Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z n:A) := by
  sorry

end SimpleAmenable

end

end OAI
end
