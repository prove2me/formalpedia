-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_tangent_interval_action
-- name    : OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:47:46.206583+00:00
-- url     : https://prove2.me/theorems/5c50591d-d1a8-48f2-8711-9671fcbf73e6
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClippedLineSlideAction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClippedLineSlideAction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem tangent_interval_action (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2)
--       (g : ∀ n, B.CoordinateWindowLaw n)
--       (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
--       (d : Fin 2)
--       (hsteps : ∀ e j, |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r)
--       (hlabels : ∀ e j,
--         (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
--          endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
--         (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
--          endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
--       (z : CutRing × CutRing) (L V : Fin 2 → CutRing)
--       (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
--       (A C : ℝ) (x y : CutRing) (hpath : TangentIntervalReach u A C x y)
--       (hcenters : ∀ t : CutRing, A ≤ ordinary t → ordinary t ≤ C → ∀ j,
--         -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ∧
--         ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ≤ ordinary r)
--       (n : ℕ) (q : Fin 2 → ℤ)
--       (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
--         (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
--       (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hf : B.AlignedSmallSupported f)
--       (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
--       (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
--       (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
--       B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
--           (universalMap (subtypeAlternatingHom I.val) s)*t*
--         (B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
--           (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--       B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
--           (universalMap (subtypeAlternatingHom I.val) s)*t*
--         (B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
--           (universalMap (subtypeAlternatingHom I.val) s))⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.endpointLabel`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.universalMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.controlAlphabet_perfect` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.coordinateWindowPrimitives`, `OAI.SimpleAmenable.pointCoordinate`, `OAI.SimpleAmenable.tangentOffset`, `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw`, `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.TangentIntervalReach` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.coordinateRectangle` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.clippingOverlapLower`, `OAI.SimpleAmenable.clippingOverlapUpper`, `OAI.SimpleAmenable.signedShortSteps`, `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported`, `OAI.SimpleAmenable.InitialCoverSystem.TangentChartLaws` and `OAI.SimpleAmenable.InitialCoverSystem.tangentSign` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClippedLineSlideAction.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.tangent_interval_action)

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ClippedLineSlideAction
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_interval_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2)
    (hsteps : ∀ e j, |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r)
    (hlabels : ∀ e j,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
    (z : CutRing × CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (A C : ℝ) (x y : CutRing) (hpath : TangentIntervalReach u A C x y)
    (hcenters : ∀ t : CutRing, A ≤ ordinary t → ordinary t ≤ C → ∀ j,
      -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ≤ ordinary r)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  sorry

end InitialCoverSystem
end ClippedLineSlideAction

end SimpleAmenable
end
end

end OAI
end
