-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_grpObj_of_mono
-- name    : GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_grpObj_of_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:45.04375+00:00
-- url     : https://prove2.me/theorems/d381b5b8-8278-4fdd-b66a-0209a845750b
-- title:
--   Sub Grp: exists grp Obj of mono
-- statement:
--   The Sub Grp construction uses the exists grp Obj of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L58-L77

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by sorry
