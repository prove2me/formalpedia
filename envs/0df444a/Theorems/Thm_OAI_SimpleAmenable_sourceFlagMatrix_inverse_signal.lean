-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_sourceFlagMatrix_inverse_signal
-- name    : OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:27:19.11951+00:00
-- url     : https://prove2.me/theorems/a58e3535-65ae-4b74-96fe-ef5314a3bea2
-- title:
--   OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalRemainder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalRemainder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical Filter Matrix`, `open scoped Topology`):
--
--   ```lean
--   theorem sourceFlagMatrix_inverse_signal {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
--       (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
--       (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
--       (hL : 0<L) (hKL : K+2 ≤ L)
--       (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
--       (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
--       (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
--       (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
--       ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
--         ∀ε : ℝ,0<ε → ∀ᶠn : ℕ in atTop,
--           ∀T : Finset (FlagSite a m D v),
--             flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)⊆T →
--             finiteL2Norm (((1 : Matrix T T ℝ)+(Matrix.of (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val)))⁻¹*ᵥ
--               (fun z : T => flagSignalDifference (v:=v) hD g (fun x => q+ψ x) (sourceDyadicN n) z.val)) ≤
--                 C₁*η+C₂*Real.sqrt κ+ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.finiteL2Norm`, `OAI.SimpleAmenable.sourceDyadicN` and `OAI.SimpleAmenable.sourceDyadicN_pos` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.FlagSite` and `OAI.SimpleAmenable.flagBoxFinset` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.sourceFlagMatrix` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.flagSignalDifference` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.finiteSignalFields_transport` and `OAI_SimpleAmenable_jointBitFieldLaw_transport` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalRemainder.lean (declaration OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonSignalInverse
open Classical Filter Matrix
open scoped Topology

theorem sourceFlagMatrix_inverse_signal {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀ε : ℝ,0<ε → ∀ᶠn : ℕ in atTop,
        ∀T : Finset (FlagSite a m D v),
          flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)⊆T →
          finiteL2Norm (((1 : Matrix T T ℝ)+(Matrix.of (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val)))⁻¹*ᵥ
            (fun z : T => flagSignalDifference (v:=v) hD g (fun x => q+ψ x) (sourceDyadicN n) z.val)) ≤
              C₁*η+C₂*Real.sqrt κ+ε := by
  sorry

end PolygonSignalInverse

end SimpleAmenable
end
end

end OAI
end
