-- Prove2me | Theorems.Thm_OAI_IntervalBar_Diagram_first_row_two_finite
-- name    : OAI.IntervalBar.Diagram.first_row_two_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:22:19.711949+00:00
-- url     : https://prove2.me/theorems/c24796ea-807a-401a-9f48-3f3257912317
-- title:
--   OAI.IntervalBar.Diagram.first_row_two_finite: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IntervalBar.Diagram.first_row_two_finite` of [lean/OAI/GroupTheory/SimpleAmenable/Simplicial/FirstBarDegreeTwoFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/FirstBarDegreeTwoFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IntervalBar.Diagram`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex`, `open FreeChains ComponentTranslation MarkedH1`):
--
--   ```lean
--   lemma first_row_two_finite
--       [Module.Finite ℤ ((bar (C:=C)).homology Z 1:A)]
--       [Module.Finite ℤ ((bar (C:=C)).homology Z 2:A)]
--       [Module.Finite ℤ ((bar (C:=C)).homology Z 3:A)] :
--       Module.Finite ℤ ((homologyRow (C:=C) 2).homology 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A`, `OAI.FreeChains.Z` and `OAI.IntervalBar.Diagram.bar` (definitions bundle `OAIQ65Sa000` of this split); `OAI.IntervalBar.Diagram.homologyRow` (definitions bundle `OAIQ65Sa004` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_PolygonTracks_fullH2_finite_of_bar` and `OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/FirstBarDegreeTwoFinite.lean (declaration OAI.IntervalBar.Diagram.first_row_two_finite)

import Mathlib
import Definitions.Def_OAIQ65Sa004

section

attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace IntervalBar.Diagram
open FreeChains ComponentTranslation MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma first_row_two_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 3:A)] :
    Module.Finite ℤ ((homologyRow (C:=C) 2).homology 1) := by
  sorry
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite

end OAI
end
