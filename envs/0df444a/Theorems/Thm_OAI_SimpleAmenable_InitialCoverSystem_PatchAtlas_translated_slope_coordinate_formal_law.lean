-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_translated_slope_coordinate_formal_law
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:21:59.788305+00:00
-- url     : https://prove2.me/theorems/b8af226a-1fc2-4ca5-8e55-90d85470d9de
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FormalLawCovariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FormalLawCovariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem translated_slope_coordinate_formal_law (hlarge : 25 ≤ m+1)
--       (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
--       (d j : Fin 2) (u v : CutRing × CutRing) :
--       HasCentralLaw (smallFamilyModel (fun i : Fin 2 => {σ : Fin 2 → Bool | σ i=true}))
--         (smallFamilyEval (B.smallPrimitiveInputs (by omega)
--           ![(slopeTestIndex d,u),(coordinateTestIndex j,v)])).rangeRestrict
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.HasCentralLaw`, `OAI.SimpleAmenable.SmallFamilyLabel`, `OAI.SimpleAmenable.SmallFamilyWord`, `OAI.SimpleAmenable.coordinateTestIndex`, `OAI.SimpleAmenable.slopeTestIndex` and `OAI.SimpleAmenable.smallFamilyEval` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.smallFamilyModel` and `OAI.SimpleAmenable.InitialCoverSystem.smallPrimitiveInputs` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` (definitions bundle `OAIQ65Sa013` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.primitive_laws_eventually` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/FormalLawCovariance.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law)

import Mathlib
import Definitions.Def_OAIQ65Sa013

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FormalLawCovariance
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

namespace PatchAtlas
variable {B} (A : B.PatchAtlas)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

include A in

theorem translated_slope_coordinate_formal_law (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (u v : CutRing × CutRing) :
    HasCentralLaw (smallFamilyModel (fun i : Fin 2 => {σ : Fin 2 → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega)
        ![(slopeTestIndex d,u),(coordinateTestIndex j,v)])).rangeRestrict := by
  sorry

end PatchAtlas
end InitialCoverSystem
end FormalLawCovariance

end SimpleAmenable
end
end

end OAI
end
