-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_jointBitFieldLaw_success
-- name    : OAI.SimpleAmenable.jointBitFieldLaw_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:25:35.293485+00:00
-- url     : https://prove2.me/theorems/a546bdd0-0e4f-4bda-ae98-5723bb0aa500
-- title:
--   OAI.SimpleAmenable.jointBitFieldLaw_success: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.jointBitFieldLaw_success` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical MeasureTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem jointBitFieldLaw_success {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
--       (S : Fin k → FieldSignalData) (hD : 0<D) {η κ : ℝ} (hη : 0<η) (hκ : 0<κ) :
--       Tendsto (fun n => (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).real
--         {b | ¬jointFieldSuccess v S n b}) atTop (nhds 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.FieldSignalData` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.FlagSite` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.jointBitFieldLaw` and `OAI.SimpleAmenable.jointFieldSuccess` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean (declaration OAI.SimpleAmenable.jointBitFieldLaw_success)

import Mathlib
import Definitions.Def_OAIQ65Sa014

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

section JointFieldSuccess
open Classical MeasureTheory Filter Set
open scoped Topology

theorem jointBitFieldLaw_success {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) {η κ : ℝ} (hη : 0<η) (hκ : 0<κ) :
    Tendsto (fun n => (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).real
      {b | ¬jointFieldSuccess v S n b}) atTop (nhds 0) := by
  sorry

end JointFieldSuccess

end SimpleAmenable
end
end

end OAI
end
