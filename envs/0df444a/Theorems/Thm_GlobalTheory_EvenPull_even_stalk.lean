-- Prove2me | Theorems.Thm_GlobalTheory_EvenPull_even_stalk
-- name    : GlobalTheory.EvenPull.even_stalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:10.079829+00:00
-- url     : https://prove2.me/theorems/fdcc737d-1882-4caa-b227-82d0d58bffde
-- title:
--   Even Pull: even stalk
-- statement:
--   The Even Pull construction uses the even stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L89-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull

theorem GlobalTheory.EvenPull.even_stalk {T G B Z : Scheme.{0}} {L : LB G} {M : LB B} {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G}
    {iB : B ⟶ B} (w : LB.Iso (L.pull f) (M.pull p))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι)
    (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
    (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
    (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
    (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS) (r : Z ⟶ T) (z : Z) (hz : r z ∈ V) :
    gm r z V (res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1))) =
      gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) * gw w r z (jT 1) (fun _ => jS 1) ∧
    gm r z V (res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))) =
      gw w (r ≫ iT) z (jT 0) (fun _ => jS 0) * gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) := by sorry
