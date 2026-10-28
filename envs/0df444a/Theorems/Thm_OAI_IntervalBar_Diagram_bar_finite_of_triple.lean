-- Prove2me | Theorems.Thm_OAI_IntervalBar_Diagram_bar_finite_of_triple
-- name    : OAI.IntervalBar.Diagram.bar_finite_of_triple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:30:38.261633+00:00
-- url     : https://prove2.me/theorems/4afa4e10-14a7-4ab6-a584-61fc56abdd5d
-- title:
--   OAI.IntervalBar.Diagram.bar_finite_of_triple: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IntervalBar.Diagram.bar_finite_of_triple` of [lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarRowFiniteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarRowFiniteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IntervalBar.Diagram`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains BarFinitePower SimplicialDiagonal`):
--
--   ```lean
--   lemma bar_finite_of_triple
--       (hf:∀n,n≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
--       ∀q,q≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z q : A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A`, `OAI.FreeChains.Z` and `OAI.IntervalBar.Diagram.bar` (definitions bundle `OAIQ65Sa000` of this split); `OAI.IntervalBar.Diagram.bar₃` (definitions bundle `OAIQ65Sa004` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_polygon_alternating_H2_finite` and `OAI.SimpleAmenable.polygon_bar_homology_finite` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarRowFiniteness.lean (declaration OAI.IntervalBar.Diagram.bar_finite_of_triple)

import Mathlib
import Definitions.Def_OAIQ65Sa004

section

attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains BarFinitePower SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar_finite_of_triple
    (hf:∀n,n≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
    ∀q,q≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z q : A) := by
  sorry
end IntervalBar.Diagram

end

end OAI
end
