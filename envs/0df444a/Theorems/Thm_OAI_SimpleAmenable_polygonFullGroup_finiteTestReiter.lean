-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_polygonFullGroup_finiteTestReiter
-- name    : OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:23:07.131616+00:00
-- url     : https://prove2.me/theorems/e91e9658-665d-41aa-b810-f97613dc9ef2
-- title:
--   OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical MeasureTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem polygonFullGroup_finiteTestReiter {a m : ℕ} (ha : 0 < a) :
--       FiniteTestReiter (polygonFullGroup a m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FiniteTestReiter` (definitions bundle `OAIQ65Sa002` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.polygon_infinite_simple_folner` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean (declaration OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter)

import Mathlib
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002

section

attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonMatchingLaw
open Classical MeasureTheory Filter Set
open scoped Topology

theorem polygonFullGroup_finiteTestReiter {a m : ℕ} (ha : 0 < a) :
    FiniteTestReiter (polygonFullGroup a m) := by
  sorry

end PolygonMatchingLaw

end SimpleAmenable
end
end

end OAI
end
