-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_exists_add_eq_of_isCoprime
-- name    : GlobalTheory.SqZero.exists_add_eq_of_isCoprime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:39.030859+00:00
-- url     : https://prove2.me/theorems/06f16d68-5f0f-4aaf-8d8b-fa77799fabf1
-- title:
--   Sq Zero: exists add eq of is Coprime
-- statement:
--   The Sq Zero construction uses the exists add eq of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L226-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L226-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
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
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']

theorem GlobalTheory.SqZero.exists_add_eq_of_isCoprime {T₁ T₂ T₁₂ : Type} [CommRing T₁] [Algebra R T₁] [CommRing T₂]
    [Algebra R T₂] [CommRing T₁₂] [Algebra R T₁₂] {f g : T} (hfg : IsCoprime f g)
    {ρ₁ : T →ₐ[R] T₁} {ρ₂ : T →ₐ[R] T₂} {ρ : T →ₐ[R] T₁₂} (h₁ : IsAway ρ₁ f) (h₂ : IsAway ρ₂ g)
    (h : IsAway ρ (f * g)) {a : T₁ →ₐ[R] T₁₂} {b : T₂ →ₐ[R] T₁₂} (ha : a.comp ρ₁ = ρ)
    (hb : b.comp ρ₂ = ρ) {I : Ideal T} {z : T₁₂} (hz : z ∈ I.map ρ) :
    ∃ z₁ ∈ I.map ρ₁, ∃ z₂ ∈ I.map ρ₂, z = a z₁ + b z₂ := by sorry
