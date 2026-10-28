-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_ConcurrentGeometry_InwardChart_polygons_assignment_realized
-- name    : OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:34:23.432265+00:00
-- url     : https://prove2.me/theorems/823db8ae-9646-4489-81fe-8ef76a1af2cb
-- title:
--   OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/InactiveNeighborhoodActions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/InactiveNeighborhoodActions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, with `open scoped symmDiff`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem polygons_assignment_realized [Finite ι] {κ : Type*}
--       (hr : 0<ordinary r ∧ ordinary r<1/2)
--       (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
--       (R : κ → polygonAlgebra a)
--       (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val)
--       (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val)
--       (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
--       ∃ q : GenericSquare a, q.val ∈ N ∧ polygonAssignment R q=polygonAssignment (T.polygons R) p
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.AvoidsCuts`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.halfPlane`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra` and `OAI.SimpleAmenable.polygonAssignment` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.inwardMargin`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons` and `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex` (definitions bundle `OAIQ65Sa010` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.constant_model_action` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_local_templates` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/InactiveNeighborhoodActions.lean (declaration OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons_assignment_realized)

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

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {ι : Type*}

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem polygons_assignment_realized [Finite ι] {κ : Type*}
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (R : κ → polygonAlgebra a)
    (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧ polygonAssignment R q=polygonAssignment (T.polygons R) p := by
  sorry

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
end
