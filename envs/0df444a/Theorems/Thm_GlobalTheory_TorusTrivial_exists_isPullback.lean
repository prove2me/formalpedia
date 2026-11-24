-- Prove2me | Theorems.Thm_GlobalTheory_TorusTrivial_exists_isPullback
-- name    : GlobalTheory.TorusTrivial.exists_isPullback
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:11:21.103081+00:00
-- url     : https://prove2.me/theorems/523a8caf-4e48-4ced-8ad2-01d694cf03cd
-- title:
--   Torus Trivial: exists is Pullback
-- statement:
--   The Torus Trivial construction uses the exists is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L14-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L14-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial

theorem GlobalTheory.TorusTrivial.exists_isPullback {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B W V : C} [GrpObj T] [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : T ⟶ G)
    [IsMonHom q] [IsMonHom i] (hk : IsPullback i (toUnit _) q η[B])
    {j : W ⟶ G} {k : V ⟶ B} {q' : W ⟶ V} (hW : IsPullback j q' q k) [Mono j] (τ : W ⟶ T)
    (hτ : ∀ (Z : C) (t : Z ⟶ T) (g g' : Z ⟶ W), g' ≫ j = (t ≫ i) * (g ≫ j) →
      g' ≫ τ = t * (g ≫ τ)) :
    ∃ a : T ⊗ W ⟶ W, IsPullback (𝟙 _) a (T ◁ q') (lift τ q') := by sorry
