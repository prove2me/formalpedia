-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_fullH1_finite_of_bar
-- name    : OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:23:22.809463+00:00
-- url     : https://prove2.me/theorems/4da545b5-d148-46d7-8101-2fb92fd10f6f
-- title:
--   OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedReturn.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedReturn.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.PolygonTracks`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains ComponentTranslation GroupoidComponentHomology`):
--
--   ```lean
--   lemma fullH1_finite_of_bar (a m:ℕ) (hm : 32 ≤ m)
--       [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 1 : A)]
--       [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 2 : A)] :
--       Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A`, `OAI.FreeChains.Z` and `OAI.IntervalBar.Diagram.bar` (definitions bundle `OAIQ65Sa000` of this split); `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.PolygonObject`, `OAI.SimpleAmenable.PolygonObject.instGroupoid` and `OAI.SimpleAmenable.PolygonObject.monoidal` (definitions bundle `OAIQ65Sa006` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_PolygonTracks_fullH2_finite_of_bar`, `OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar`, `OAI.SimpleAmenable.main` and `OAI_SimpleAmenable_polygon_alternating_H2_finite` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedReturn.lean (declaration OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar)

import Mathlib
import Definitions.Def_OAIQ65Sa006

section

attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma fullH1_finite_of_bar (a m:ℕ) (hm : 32 ≤ m)
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 1 : A)]
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 2 : A)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) := by
  sorry
end SimpleAmenable.PolygonTracks

end

end OAI
end
