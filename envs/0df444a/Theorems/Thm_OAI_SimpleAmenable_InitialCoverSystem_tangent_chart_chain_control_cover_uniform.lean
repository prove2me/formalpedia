-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_tangent_chart_chain_control_cover_uniform
-- name    : OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:58:57.608229+00:00
-- url     : https://prove2.me/theorems/62963f19-4d9c-4228-9685-951600090a2d
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem tangent_chart_chain_control_cover_uniform (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2)
--       {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
--       (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
--       (l v : Fin 2 → CutRing)
--       (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
--       (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
--       (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
--       (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
--       (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
--       (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
--         -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
--         ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) :
--       ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
--         ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
--         ∀ L V : Fin 2 → CutRing,
--         (∀ j, ordinary (L j) ≤ ordinary (V j)) →
--         (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
--         (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
--         ∀ (d : Fin 2) (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
--         (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) →
--         (∀ i, i < T → ∀ j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
--         (∀ i, i < T → ∀ j, ordinary (l j)+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-δ) →
--         (∀ i, i < T → ∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate (z i) j)) →
--         ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
--         B.AlignedSmallSupported f →
--         (∀ j, SmallControlled B.c f
--           (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
--         SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z 0) true) →
--         SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z T) true)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.endpointLabel`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.coordinateInterval`, `OAI.SimpleAmenable.pointCoordinate`, `OAI.SimpleAmenable.pointLabel`, `OAI.SimpleAmenable.tangentOffset`, `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw` and `OAI.SimpleAmenable.InitialCoverSystem.axisSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.signedShortSteps`, `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported`, `OAI.SimpleAmenable.InitialCoverSystem.TangentChartLaws` and `OAI.SimpleAmenable.InitialCoverSystem.tangentSign` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform)

import Mathlib
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CoverUniformBridges
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_chart_chain_control_cover_uniform (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
      -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
      ∀ L V : Fin 2 → CutRing,
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
      ∀ (d : Fin 2) (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
      (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) →
      (∀ i, i < T → ∀ j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      (∀ i, i < T → ∀ j, ordinary (l j)+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-δ) →
      (∀ i, i < T → ∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate (z i) j)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z 0) true) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z T) true) := by
  sorry

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
end
