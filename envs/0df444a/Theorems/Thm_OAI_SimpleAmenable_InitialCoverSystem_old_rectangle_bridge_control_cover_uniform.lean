-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_old_rectangle_bridge_control_cover_uniform
-- name    : OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:46:59.754114+00:00
-- url     : https://prove2.me/theorems/4819d9b4-6ac1-4f60-90e1-96ffe77ab651
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem old_rectangle_bridge_control_cover_uniform (hlarge : 20 ≤ m+1)
--       {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
--       ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
--         ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p q : Fin 2 → ℤ),
--         (∀ j, ((q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
--         ∀ u v U V : Fin 2 → CutRing,
--         (∀ j, ordinary (u j) ≤ ordinary (v j)) →
--         (∀ j, ordinary (U j) ≤ ordinary (u j)-δ) →
--         (∀ j, ordinary (v j)+δ ≤ ordinary (V j)) →
--         (∀ j, ordinary (V j)-ordinary (U j) < 1) →
--         (∀ j, p j ≤ endpointLabel (u j) ∧ endpointLabel (u j) < p j+s j) →
--         (∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+s j) →
--         (∀ j, q j ≤ endpointLabel (U j) ∧ endpointLabel (U j) < q j+(n/8:ℕ)) →
--         (∀ j, q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+(n/8:ℕ)) →
--         ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
--         B.AlignedSmallSupported f →
--         (∀ j, SmallControlled B.c f
--           (B.axisSector (by omega) n h j (s j) (hs j) (p j) (coordinateInterval a j (u j) (v j)))) →
--         SmallControlled B.c f (B.windowSector (by omega) n h q (coordinateRectangle a U V))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.endpointLabel`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.coordinateInterval`, `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw`, `OAI.SimpleAmenable.InitialCoverSystem.axisSector` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.coordinateRectangle` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CoverUniformBridges.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform)

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

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
section CoverUniformBridges
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_rectangle_bridge_control_cover_uniform (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p q : Fin 2 → ℤ),
      (∀ j, ((q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      ∀ u v U V : Fin 2 → CutRing,
      (∀ j, ordinary (u j) ≤ ordinary (v j)) →
      (∀ j, ordinary (U j) ≤ ordinary (u j)-δ) →
      (∀ j, ordinary (v j)+δ ≤ ordinary (V j)) →
      (∀ j, ordinary (V j)-ordinary (U j) < 1) →
      (∀ j, p j ≤ endpointLabel (u j) ∧ endpointLabel (u j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+s j) →
      (∀ j, q j ≤ endpointLabel (U j) ∧ endpointLabel (U j) < q j+(n/8:ℕ)) →
      (∀ j, q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n h j (s j) (hs j) (p j) (coordinateInterval a j (u j) (v j)))) →
      SmallControlled B.c f (B.windowSector (by omega) n h q (coordinateRectangle a U V)) := by
  sorry

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
end
