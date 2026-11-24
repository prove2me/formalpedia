-- Prove2me | Theorems.Thm_GlobalTheory_universallyClosed_of_jointly_surjective
-- name    : GlobalTheory.universallyClosed_of_jointly_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:47.388305+00:00
-- url     : https://prove2.me/theorems/7d7300d7-1b69-4ba7-944b-953f838790a7
-- title:
--   Global Theory: universally Closed of jointly surjective
-- statement:
--   The Global Theory construction uses the universally Closed of jointly surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImage.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImage.lean#L9-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory

theorem GlobalTheory.universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by sorry
