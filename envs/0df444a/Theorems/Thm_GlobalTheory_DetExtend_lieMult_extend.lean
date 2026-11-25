-- Prove2me | Theorems.Thm_GlobalTheory_DetExtend_lieMult_extend
-- name    : GlobalTheory.DetExtend.lieMult_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:48.413402+00:00
-- url     : https://prove2.me/theorems/2cdb7691-0756-5ea2-813e-b0d70f190b11
-- title:
--   Det Extend: lie Mult extend
-- statement:
--   The Det Extend construction uses the lie Mult extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L93-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L93-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat fB pushR dualMapA)

theorem GlobalTheory.DetExtend.lieMult_extend {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {K Ω : Type} [Field K] [Field Ω]
    (i : K →+* Ω) (x : Sp K ⟶ S) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* K) (N : ℕ) :
    LieMult act (spMap i ≫ x) (i.comp τ) N ↔ LieMult act x τ N := by sorry
