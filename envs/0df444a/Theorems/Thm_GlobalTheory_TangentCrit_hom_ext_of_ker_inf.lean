-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_hom_ext_of_ker_inf
-- name    : GlobalTheory.TangentCrit.hom_ext_of_ker_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:32.685373+00:00
-- url     : https://prove2.me/theorems/a4d165eb-de0e-4730-a5d7-feb19f678d5d
-- title:
--   Tangent Crit: hom ext of ker inf
-- statement:
--   The Tangent Crit construction uses the hom ext of ker inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L208-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L208-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u

theorem GlobalTheory.TangentCrit.hom_ext_of_ker_inf {D E₁ E₂ : CommRingCat.{u}} (p₁ : D ⟶ E₁) (p₂ : D ⟶ E₂)
    (hs : Function.Surjective (Spec.map p₁)) (h : ∀ d, p₁ d = 0 → p₂ d = 0 → d = 0)
    {X : Scheme.{u}} {g g' : Spec D ⟶ X} (h₁ : Spec.map p₁ ≫ g = Spec.map p₁ ≫ g')
    (h₂ : Spec.map p₂ ≫ g = Spec.map p₂ ≫ g') : g = g' := by sorry
