-- Prove2me | Theorems.Thm_GlobalTheory_LocalWeightUnits_exists_weight_zero_sum_one
-- name    : GlobalTheory.LocalWeightUnits.exists_weight_zero_sum_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:35.271724+00:00
-- url     : https://prove2.me/theorems/1391711c-942b-4934-a353-c72acc85dc25
-- title:
--   Local Weight Units: exists weight zero sum one
-- statement:
--   The Local Weight Units construction uses the exists weight zero sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L14-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L14-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
import Theorems.Thm_GlobalTheory_UU_IsWt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.LocalWeightUnits

theorem GlobalTheory.LocalWeightUnits.exists_weight_zero_sum_one {A X J : Type} [CommRing A] [AddCommGroup X] [Fintype J] (P : X → AddSubgroup A)
    (one : 1 ∈ P 0) (mul : ∀ u v χ χ', u ∈ P χ → v ∈ P χ' → u * v ∈ P (χ + χ'))
    (ex : ∀ u : A, ∃ a : X →₀ A, (∀ χ, a χ ∈ P χ) ∧ u = a.sum fun _ x => x)
    (un : ∀ a : X →₀ A, (∀ χ, a χ ∈ P χ) → (a.sum fun _ x => x) = 0 → a = 0)
    (g : J → A) (δ : X) (hg : ∀ f, g f ∈ P δ) (hs : Ideal.span (Set.range g) = ⊤) :
    ∃ b : J → A, (∀ f, b f ∈ P 0) ∧ (∀ f, g f ∣ b f) ∧ ∑ f, b f = 1 := by sorry
