-- Prove2me | Theorems.Thm_GlobalTheory_DetExtend_lieMult_fibre
-- name    : GlobalTheory.DetExtend.lieMult_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:31.9164+00:00
-- url     : https://prove2.me/theorems/e8f21977-46ad-429a-8335-921d9874a125
-- title:
--   Det Extend: lie Mult fibre
-- statement:
--   The Det Extend construction uses the lie Mult fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L24-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
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
open GlobalTheory GlobalTheory.DetExtend

theorem GlobalTheory.DetExtend.lieMult_fibre {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) {G : Over S} [GrpObj G] {O : Type}
    [CommRing O] (a : OAct O G) (a' : OAct O ((Over.pullback x).obj G))
    (h : ∀ c, a'.act c = (Over.pullback x).map (a.act c)) {k' : Type} [Field k'] (y : Sp k' ⟶ Sp k)
    (τ : O →+* k') (n : ℕ) : LieMult a' y τ n ↔ LieMult a (y ≫ x) τ n := by sorry
