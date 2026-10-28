-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_PolygonTracks_finite_alternating_H2_of_full
-- name    : OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:20:59.168537+00:00
-- url     : https://prove2.me/theorems/cdad0fac-a210-47b0-9821-ab8e676ae271
-- title:
--   OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full` of [lean/OAI/GroupTheory/SimpleAmenable/Homology/FullH2.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/FullH2.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.PolygonTracks`, with `open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep`):
--
--   ```lean
--   lemma finite_alternating_H2_of_full (a m : ℕ) (hm : 205 < m)
--       [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1)]
--       [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2)] :
--       Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.polygonAlternatingGroup` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.IntegralHomology.coefficients` (definitions bundle `OAIQ65Sa002` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.main` and `OAI_SimpleAmenable_polygon_alternating_H2_finite` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/FullH2.lean (declaration OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full)

import Mathlib
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002

section

attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace PolygonTracks

lemma finite_alternating_H2_of_full (a m : ℕ) (hm : 205 < m)
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1)]
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2)] :
    Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m))) := by
  sorry
end PolygonTracks
end SimpleAmenable

end OAI
end
