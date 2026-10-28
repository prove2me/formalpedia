-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_stableH2_finite_of_bar
-- name    : OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:23:46.936093+00:00
-- url     : https://prove2.me/theorems/66885617-97b9-4ff9-88bd-b7d1fac0efe1
-- title:
--   OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar` of [lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarBinaryBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarBinaryBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.PolygonTracks`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains ComponentStable IntervalBar.Diagram`):
--
--   ```lean
--   lemma stableH2_finite_of_bar (a:ℕ)
--       [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
--       [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
--       [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
--       Module.Finite ℤ (object (C:=PolygonObject a) 2:A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A`, `OAI.FreeChains.Z` and `OAI.IntervalBar.Diagram.bar` (definitions bundle `OAIQ65Sa000` of this split); `OAI.ComponentStable.object` (definitions bundle `OAIQ65Sa004` of this split); `OAI.SimpleAmenable.PolygonObject`, `OAI.SimpleAmenable.PolygonObject.instGroupoid` and `OAI.SimpleAmenable.PolygonObject.monoidal` (definitions bundle `OAIQ65Sa006` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.main` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/BarBinaryBoundary.lean (declaration OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar)

import Mathlib
import Definitions.Def_OAIQ65Sa004
import Definitions.Def_OAIQ65Sa006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentStable IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma stableH2_finite_of_bar (a:ℕ)
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
    Module.Finite ℤ (object (C:=PolygonObject a) 2:A) := by
  sorry
end SimpleAmenable.PolygonTracks

end

end OAI
end
