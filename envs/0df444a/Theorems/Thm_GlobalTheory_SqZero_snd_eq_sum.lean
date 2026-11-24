-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_snd_eq_sum
-- name    : GlobalTheory.SqZero.snd_eq_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:29:26.105808+00:00
-- url     : https://prove2.me/theorems/1060db99-5734-40c0-806b-66f1fb8f1b2b
-- title:
--   Sq Zero: snd eq sum
-- statement:
--   The Sq Zero construction uses the snd eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L243-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L243-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
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
variable {R : Type} [CommRing R]
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem GlobalTheory.SqZero.snd_eq_sum {B κ : Type} [CommRing B] [Algebra R B] [Fintype κ] {β : κ → B}
    {τ : κ → Derivation R B B}
    (hτ : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : B →ₐ[R] A),
        (∀ b b', (φ b - φ' b) * (φ b' - φ' b') = 0) →
        ∀ b, φ b - φ' b = ∑ i, φ' (τ i b) * (φ (β i) - φ' (β i)))
    (u : B →ₐ[R] S) (φ : B →ₐ[R] DualNumber S) (hφ : ∀ b, (φ b).fst = u b) (b : B) :
    (φ b).snd = ∑ i, u (τ i b) * (φ (β i)).snd := by sorry
