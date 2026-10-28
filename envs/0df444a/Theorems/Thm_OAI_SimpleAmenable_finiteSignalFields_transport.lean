-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_finiteSignalFields_transport
-- name    : OAI.SimpleAmenable.finiteSignalFields_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:49:59.953982+00:00
-- url     : https://prove2.me/theorems/991bbeca-a655-4799-b28f-28d2cd97d64f
-- title:
--   OAI.SimpleAmenable.finiteSignalFields_transport: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.finiteSignalFields_transport` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem finiteSignalFields_transport {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
--       (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
--       {ε : ℝ} (hε : 0<ε) :
--       ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,∀j,
--         ObservableClose ((S j).bitLaw (v:=v j) hD η κ n)
--           (((S j).bitLaw (v:=v j) hD η κ n).map (bitReindex (flagSitePermutation hD g))) ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FieldSignalData`, `OAI.SimpleAmenable.ObservableClose` and `OAI.SimpleAmenable.bitReindex` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.FlagSite` and `OAI.SimpleAmenable.flagSitePermutation` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.FieldSignalData.bitLaw` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/JointBitField.lean (declaration OAI.SimpleAmenable.finiteSignalFields_transport)

import Mathlib
import Definitions.Def_OAIQ65Sa011

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
section JointBitField
open Classical MeasureTheory Filter
open scoped Topology

theorem finiteSignalFields_transport {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
    {ε : ℝ} (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,∀j,
      ObservableClose ((S j).bitLaw (v:=v j) hD η κ n)
        (((S j).bitLaw (v:=v j) hD η κ n).map (bitReindex (flagSitePermutation hD g))) ε := by
  sorry

end JointBitField

end SimpleAmenable
end
end

end OAI
end
