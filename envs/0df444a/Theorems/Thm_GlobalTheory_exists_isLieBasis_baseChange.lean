-- Prove2me | Theorems.Thm_GlobalTheory_exists_isLieBasis_baseChange
-- name    : GlobalTheory.exists_isLieBasis_baseChange
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:03.701642+00:00
-- url     : https://prove2.me/theorems/44dda8fa-7aad-49e2-a7c2-4e0b4257d70f
-- title:
--   Global Theory: exists is Lie Basis base Change
-- statement:
--   The Global Theory construction uses the exists is Lie Basis base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsLieBasisBaseChange.lean#L118-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsLieBasisBaseChange.lean#L118-L130

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
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)

theorem GlobalTheory.exists_isLieBasis_baseChange (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by sorry
