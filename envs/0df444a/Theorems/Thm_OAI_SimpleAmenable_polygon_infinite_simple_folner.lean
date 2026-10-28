-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_polygon_infinite_simple_folner
-- name    : OAI.SimpleAmenable.polygon_infinite_simple_folner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T01:26:00.745542+00:00
-- url     : https://prove2.me/theorems/30fa4f96-bce0-47ad-bcb4-bf15fe49008d
-- title:
--   OAI.SimpleAmenable.polygon_infinite_simple_folner: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.polygon_infinite_simple_folner` of [lean/OAI/GroupTheory/SimpleAmenable/Amenability/SubgroupTestReiter.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/SubgroupTestReiter.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem polygon_infinite_simple_folner {a m : ℕ} (ha : 0 < a) (hm : 15 ≤ m) :
--       Infinite (polygonAlternatingGroup a m) ∧ IsSimpleGroup (polygonAlternatingGroup a m) ∧
--       FolnerAmenable (polygonAlternatingGroup a m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.polygonAlternatingGroup` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FolnerAmenable` (the published bundle `Def_SimpleAmenable`).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.main` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/SubgroupTestReiter.lean (declaration OAI.SimpleAmenable.polygon_infinite_simple_folner)

import Mathlib
import Definitions.Def_SimpleAmenable
import Definitions.Def_OAIQ65Sa001

section

attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PolygonAmenability

theorem polygon_infinite_simple_folner {a m : ℕ} (ha : 0 < a) (hm : 15 ≤ m) :
    Infinite (polygonAlternatingGroup a m) ∧ IsSimpleGroup (polygonAlternatingGroup a m) ∧
    FolnerAmenable (polygonAlternatingGroup a m) := by
  sorry

end PolygonAmenability

end SimpleAmenable
end
end

end OAI
end
