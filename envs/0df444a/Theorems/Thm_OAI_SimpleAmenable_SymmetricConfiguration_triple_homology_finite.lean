-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_SymmetricConfiguration_triple_homology_finite
-- name    : OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:39:40.086254+00:00
-- url     : https://prove2.me/theorems/fc6e9b09-ac3c-4eee-b8d9-88e3e7c0e479
-- title:
--   OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.SymmetricConfiguration`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite`, `open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject`):
--
--   ```lean
--   lemma triple_homology_finite (n:ℕ) (hn:n≤5) :
--       Module.Finite ℤ ((IntervalBar.Diagram.bar₃ (C:=FiniteSetGroupoid)).homology Z n:A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FreeChains.A` and `OAI.FreeChains.Z` (definitions bundle `OAIQ65Sa000` of this split); `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid` and `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instGroupoid` (definitions bundle `OAIQ65Sa002` of this split); `OAI.IntervalBar.Diagram.bar₃` (definitions bundle `OAIQ65Sa004` of this split); `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.monoidal` and `OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.symmetric` (definitions bundle `OAIQ65Sa008` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_polygon_alternating_H2_finite` and `OAI.SimpleAmenable.polygon_bar_homology_finite` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean (declaration OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite)

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
lemma triple_homology_finite (n:ℕ) (hn:n≤5) :
    Module.Finite ℤ ((IntervalBar.Diagram.bar₃ (C:=FiniteSetGroupoid)).homology Z n:A) := by
  sorry
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end
