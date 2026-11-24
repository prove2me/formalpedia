-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_kerEquiv_map
-- name    : GlobalTheory.SqZero.kerEquiv_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:54.284362+00:00
-- url     : https://prove2.me/theorems/36b3db23-686c-4a14-9233-9a329875d7c0
-- title:
--   Sq Zero: ker Equiv map
-- statement:
--   The Sq Zero construction uses the ker Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L108-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L108-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
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

theorem GlobalTheory.SqZero.kerEquiv_map (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {J' : Ideal A'}
    (hJ' : J' ^ 2 = ⊥) (φ : A →ₐ[R] A') (hφ : ∀ a ∈ J, φ a ∈ J') (y : redKer (R := R) G J)
    (i : Fin n) :
    (kerEquiv hv hJ' (Additive.ofMul ⟨spMap φ ≫ y.1, comp_mem_redKer y.2 φ hφ⟩) i : A') =
      φ (kerEquiv hv hJ (Additive.ofMul y) i) := by sorry
