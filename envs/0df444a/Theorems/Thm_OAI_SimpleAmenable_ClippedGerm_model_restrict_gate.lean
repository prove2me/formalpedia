-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_ClippedGerm_model_restrict_gate
-- name    : OAI.SimpleAmenable.ClippedGerm.model_restrict_gate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:40:38.827993+00:00
-- url     : https://prove2.me/theorems/e38db37e-3bdd-420d-a640-e47cf324094c
-- title:
--   OAI.SimpleAmenable.ClippedGerm.model_restrict_gate: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.ClippedGerm.model_restrict_gate` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/ClippedGerms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/ClippedGerms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.ClippedGerm`, with `open scoped symmDiff`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem model_restrict_gate {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
--       {j : ι → Fin 4} {c : ι → CutRing}
--       (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
--       (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
--       (lo hi : Fin 2 → ι) (s : ι)
--       (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
--       (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
--       (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
--       (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
--         (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
--       (σ : Fin 2 × Bool → Bool) :
--       T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) () ⊓
--         C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ =
--       (if ∀ d, σ (d,false)=false ∧ σ (d,true)=true then
--         (C.localDecision T.vertex T.offset z (j s) (c s))ᶜ else ⊥) ⊓
--         C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.clippedSlopePrimitive`, `OAI.SimpleAmenable.halfPlane`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary` and `OAI.SimpleAmenable.polygonAlgebra` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy` and `OAI.SimpleAmenable.axisDirection` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.pointCoordinate` and `OAI.SimpleAmenable.spatialTranslate` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.ClippedGerm`, `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.ClippedGerm.axialCut`, `OAI.SimpleAmenable.ClippedGerm.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.coordinateGate`, `OAI.SimpleAmenable.ConcurrentGeometry.localDecision`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons` and `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex` (definitions bundle `OAIQ65Sa010` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.exterior_clipped_model_action` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/ClippedGerms.lean (declaration OAI.SimpleAmenable.ClippedGerm.model_restrict_gate)

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

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

theorem model_restrict_gate {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (σ : Fin 2 × Bool → Bool) :
    T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) () ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ =
    (if ∀ d, σ (d,false)=false ∧ σ (d,true)=true then
      (C.localDecision T.vertex T.offset z (j s) (c s))ᶜ else ⊥) ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ := by
  sorry

end ClippedGerm

end SimpleAmenable

end OAI
end
