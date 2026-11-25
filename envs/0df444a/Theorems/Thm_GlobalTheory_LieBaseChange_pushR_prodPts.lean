-- Prove2me | Theorems.Thm_GlobalTheory_LieBaseChange_pushR_prodPts
-- name    : GlobalTheory.LieBaseChange.pushR_prodPts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:54:44.105945+00:00
-- url     : https://prove2.me/theorems/4f9af0f6-8c84-496b-8244-bc70b859d12e
-- title:
--   Lie Base Change: push R prod Pts
-- statement:
--   The Lie Base Change construction uses the push R prod Pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsLieBasisBaseChange.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsLieBasisBaseChange.lean#L61-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieBaseChange
open GlobalTheory.SqZero
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
variable {G} {n : ℕ}

theorem GlobalTheory.LieBaseChange.pushR_prodPts [IsCommMonObj G] (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R') :
    pushR G (prodPts c (bcVec R' v)) =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by sorry
