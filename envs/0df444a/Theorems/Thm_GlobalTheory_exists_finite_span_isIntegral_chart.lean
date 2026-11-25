-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_span_isIntegral_chart
-- name    : GlobalTheory.exists_finite_span_isIntegral_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:06.317602+00:00
-- url     : https://prove2.me/theorems/e81862ed-8c09-5556-b219-e6178d12da05
-- title:
--   Global Theory: exists finite span is Integral chart
-- statement:
--   The Global Theory construction uses the exists finite span is Integral chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L12-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L12-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}

theorem GlobalTheory.exists_finite_span_isIntegral_chart [IsDedekindDomain o] [CharZero Ω] [Finite J]
    (t : J → Ω) {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ G : Set Ω, G.Finite ∧
      (∀ x ∈ G, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ x, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x →
        x ∈ Submodule.span (Algebra.adjoin o (Set.range fun j => t j / t i)) G := by sorry
