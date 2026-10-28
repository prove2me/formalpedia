-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_initialCoverSystem_eventually
-- name    : OAI.SimpleAmenable.initialCoverSystem_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:27:56.15312+00:00
-- url     : https://prove2.me/theorems/e8b0c43f-51f0-4db8-bb59-7fddffea0d69
-- title:
--   OAI.SimpleAmenable.initialCoverSystem_eventually: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.initialCoverSystem_eventually` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/InitialCoverSystem.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/InitialCoverSystem.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem initialCoverSystem_eventually (a : ℕ) (r : CutRing) (m : ℕ)
--       (hm : 2 ≤ m) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
--       ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Nonempty (InitialCoverSystem a r m hm M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing` and `OAI.SimpleAmenable.ordinary` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.InitialCoverSystem` (definitions bundle `OAIQ65Sa005` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.fixed_track_polygon_progress` and `OAI_SimpleAmenable_polygon_central_cover` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/InitialCoverSystem.lean (declaration OAI.SimpleAmenable.initialCoverSystem_eventually)

import Mathlib
import Definitions.Def_OAIQ65Sa005

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section InitialCoverSystem

theorem initialCoverSystem_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Nonempty (InitialCoverSystem a r m hm M) := by
  sorry

end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
end
