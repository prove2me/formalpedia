-- Prove2me | Theorems.Thm_GlobalTheory_LevelFibre_exists_tate_push
-- name    : GlobalTheory.LevelFibre.exists_tate_push
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:11.19023+00:00
-- url     : https://prove2.me/theorems/2576dbe1-1504-40b5-ba3b-aca4fab2fdf2
-- title:
--   Level Fibre: exists tate push
-- statement:
--   The Level Fibre construction uses the exists tate push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L170-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L170-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.LevelFibre.exists_tate_push
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S') (z : Sp k ⟶ S) (hz : x ≫ f = z) (e : (Over.mk x ⟶ t'.G) ≃* (Over.mk z ⟶ t.G))
    (he : ∀ p, (e p).left = p.left ≫ m.φ)
    (I : TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), J.ζ = I.ζ ∧ ∀ n a, J.ev n a = e (I.ev n a) := by sorry
