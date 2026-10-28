-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_SymmetricConfiguration_componentStableH1_finite
-- name    : OAI.SimpleAmenable.SymmetricConfiguration.componentStableH1_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:37:09.192459+00:00
-- url     : https://prove2.me/theorems/acd3c7da-c1fc-4abc-9b31-4f80e3d376fb
-- title:
--   OAI.SimpleAmenable.SymmetricConfiguration.componentStableH1_finite: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.SymmetricConfiguration.componentStableH1_finite` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.SymmetricConfiguration`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject`):
--
--   ```lean
--   lemma componentStableH1_finite : Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) 1:A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid` and `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instGroupoid` (definitions bundle `OAIQ65Sa002` of this split); `OAI.ComponentStable.object` (definitions bundle `OAIQ65Sa004` of this split); `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidal` (definitions bundle `OAIQ65Sa008` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean (declaration OAI.SimpleAmenable.SymmetricConfiguration.componentStableH1_finite)

import Mathlib
import Definitions.Def_OAIQ65Sa008

section

attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
lemma componentStableH1_finite : Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) 1:A) := by
  sorry
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end
