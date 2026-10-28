-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_binaryD_quotient_zero
-- name    : OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:40:06.582874+00:00
-- url     : https://prove2.me/theorems/06108282-863d-4a88-a8f2-6913b0e5eeb5
-- title:
--   OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/FiberBinary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/FiberBinary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.PolygonTracks`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains ComponentTranslation ComponentStable`):
--
--   ```lean
--   lemma binaryD_quotient_zero (a:ℕ) : binaryD (C:=PolygonObject a) 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A` and `OAI.FreeChains.Z` (definitions bundle `OAIQ65Sa000` of this split); `OAI.ComponentTranslation.P` (definitions bundle `OAIQ65Sa001` of this split); `OAI.ComponentStable.binaryD`, `OAI.ComponentStable.object` and `OAI.ComponentTranslation.homologyDiagram` (definitions bundle `OAIQ65Sa004` of this split); `OAI.SimpleAmenable.PolygonObject`, `OAI.SimpleAmenable.PolygonObject.instGroupoid` and `OAI.SimpleAmenable.PolygonObject.monoidal` (definitions bundle `OAIQ65Sa006` of this split); `OAI.SimpleAmenable.PolygonTracks.mixedImage` (definitions bundle `OAIQ65Sa021` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_PolygonTracks_fullH2_finite_of_bar` and `OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/FiberBinary.lean (declaration OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero)

import Mathlib
import Definitions.Def_OAIQ65Sa021

section

attribute [-instance] _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma binaryD_quotient_zero (a:ℕ) : binaryD (C:=PolygonObject a) 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ=0 := by
  sorry
end SimpleAmenable.PolygonTracks

end OAI
end
