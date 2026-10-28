-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_CoordinateGerm_model_formula
-- name    : OAI.SimpleAmenable.CoordinateGerm.model_formula
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:39:19.738373+00:00
-- url     : https://prove2.me/theorems/cab06390-545d-4d9f-8293-4996b47a18da
-- title:
--   OAI.SimpleAmenable.CoordinateGerm.model_formula: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.CoordinateGerm.model_formula` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/CoordinateModels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/CoordinateModels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.CoordinateGerm`, with `open scoped symmDiff`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem model_formula {r : CutRing} {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
--       {j : ι → Fin 4} {c : ι → CutRing} (T : C.InwardChart j c z)
--       (hr : 0<ordinary r ∧ ordinary r<1/2)
--       (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
--       (lo hi : ι) (hlo : j lo=axisDirection d ∧ c lo=G.lower)
--       (hhi : j hi=axisDirection d ∧ c hi=G.upper)
--       (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val)
--       (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
--       p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ()).val ↔
--         p ∉ (C.localDecision T.vertex T.offset z (j lo) (c lo)).val ∧
--         p ∈ (C.localDecision T.vertex T.offset z (j hi) (c hi)).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.coordinatePrimitive`, `OAI.SimpleAmenable.halfPlane`, `OAI.SimpleAmenable.ordinary` and `OAI.SimpleAmenable.polygonAlgebra` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy` and `OAI.SimpleAmenable.axisDirection` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.spatialTranslate` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.CoordinateGerm`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.inwardMargin`, `OAI.SimpleAmenable.ConcurrentGeometry.localDecision`, `OAI.SimpleAmenable.CoordinateGerm.lower`, `OAI.SimpleAmenable.CoordinateGerm.upper`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons` and `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex` (definitions bundle `OAIQ65Sa010` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/CoordinateModels.lean (declaration OAI.SimpleAmenable.CoordinateGerm.model_formula)

import Mathlib
import Definitions.Def_OAIQ65Sa010

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section CoordinateModels

namespace CoordinateGerm
variable {a : ℕ} {d : Fin 2} {u : CutRing × CutRing} {z : ℝ × ℝ} (G : CoordinateGerm a d u z)

theorem model_formula {r : CutRing} {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing} (T : C.InwardChart j c z)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ι) (hlo : j lo=axisDirection d ∧ c lo=G.lower)
    (hhi : j hi=axisDirection d ∧ c hi=G.upper)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ()).val ↔
      p ∉ (C.localDecision T.vertex T.offset z (j lo) (c lo)).val ∧
      p ∈ (C.localDecision T.vertex T.offset z (j hi) (c hi)).val := by
  sorry

end CoordinateGerm

end CoordinateModels

end SimpleAmenable

end OAI
end
