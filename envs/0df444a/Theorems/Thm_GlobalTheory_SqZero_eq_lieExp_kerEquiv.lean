-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_eq_lieExp_kerEquiv
-- name    : GlobalTheory.SqZero.eq_lieExp_kerEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:31.249885+00:00
-- url     : https://prove2.me/theorems/485dd883-526f-4d75-a490-68544d1d253a
-- title:
--   Sq Zero: eq lie Exp ker Equiv
-- statement:
--   The Sq Zero construction uses the eq lie Exp ker Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L100-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
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
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]

theorem GlobalTheory.SqZero.eq_lieExp_kerEquiv (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    (y : redKer (R := R) G J) : (y : sp A ⟶ G) =
      lieExp v (fun i => (kerEquiv hv hJ (Additive.ofMul y) i : A))
        (fun _ => mul_eq_zero_of_sq hJ (Subtype.prop _) (Subtype.prop _)) := by sorry
