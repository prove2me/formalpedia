-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_expBij_of_unitInChart
-- name    : GlobalTheory.SqZero.expBij_of_unitInChart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:26.249932+00:00
-- url     : https://prove2.me/theorems/8d02596a-eebd-47b6-83bb-4bac11f13de9
-- title:
--   Sq Zero: exp Bij of unit In Chart
-- statement:
--   The Sq Zero construction uses the exp Bij of unit In Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AwayToAwayRightEqOfComp.lean#L87-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AwayToAwayRightEqOfComp.lean#L87-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]

theorem GlobalTheory.SqZero.expBij_of_unitInChart (hv : ∀ i, IsTangent (v i)) (hS : UnitInChart G S)
    (h : IsLieBasisOver S v) (α : S →ₐ[R] A) : ExpBij A v := by sorry
