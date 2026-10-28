-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_fixed_track_polygon_progress
-- name    : OAI.SimpleAmenable.fixed_track_polygon_progress
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:21:18.834213+00:00
-- url     : https://prove2.me/theorems/2f9c993f-2348-4b64-a5cb-80692130a292
-- title:
--   OAI.SimpleAmenable.fixed_track_polygon_progress: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.fixed_track_polygon_progress` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedTrackProgress.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedTrackProgress.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem fixed_track_polygon_progress :
--       ∃ a : ℕ, 0 < a ∧
--         ∀ m : ℕ, 100 ≤ m →
--           Infinite (polygonAlternatingGroup a m) ∧
--           IsSimpleGroup (polygonAlternatingGroup a m) ∧
--           FolnerAmenable (polygonAlternatingGroup a m) ∧
--           ∃ (H : Type) (_ : Group H) (q : H →* polygonAlternatingGroup a m),
--             Group.IsFinitelyPresented H ∧ Function.Surjective q ∧ q.ker ≤ Subgroup.center H
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.polygonAlternatingGroup` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FolnerAmenable` (the published bundle `Def_SimpleAmenable`).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.main` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonFixedTrackProgress.lean (declaration OAI.SimpleAmenable.fixed_track_polygon_progress)

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
section PolygonFixedTrackProgress

theorem fixed_track_polygon_progress :
    ∃ a : ℕ, 0 < a ∧
      ∀ m : ℕ, 100 ≤ m →
        Infinite (polygonAlternatingGroup a m) ∧
        IsSimpleGroup (polygonAlternatingGroup a m) ∧
        FolnerAmenable (polygonAlternatingGroup a m) ∧
        ∃ (H : Type) (_ : Group H) (q : H →* polygonAlternatingGroup a m),
          Group.IsFinitelyPresented H ∧ Function.Surjective q ∧ q.ker ≤ Subgroup.center H := by
  sorry

end PolygonFixedTrackProgress

end SimpleAmenable
end
end

end OAI
end
