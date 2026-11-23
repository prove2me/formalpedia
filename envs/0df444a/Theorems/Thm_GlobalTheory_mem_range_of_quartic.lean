-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_of_quartic
-- name    : GlobalTheory.mem_range_of_quartic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:45.557068+00:00
-- url     : https://prove2.me/theorems/b01027a7-1490-4e2f-9e6a-84eee2229a56
-- title:
--   Global Theory: mem range of quartic
-- statement:
--   The Global Theory construction uses the mem range of quartic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIntegralModelOfForms.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIntegralModelOfForms.lean#L62-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]
variable {A}

theorem GlobalTheory.mem_range_of_quartic {x c₀ c₁ c₂ c₃ : K} (h₀ : c₀ ∈ (algebraMap A K).range)
    (h₁ : c₁ ∈ (algebraMap A K).range) (h₂ : c₂ ∈ (algebraMap A K).range)
    (h₃ : c₃ ∈ (algebraMap A K).range) (h : x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0) :
    x ∈ (algebraMap A K).range := by sorry
