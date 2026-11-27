-- Prove2me | Theorems.Thm_GlobalTheory_exists_tuple_normalisation_charts
-- name    : GlobalTheory.exists_tuple_normalisation_charts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:16.023827+00:00
-- url     : https://prove2.me/theorems/54fff478-9ad1-5c2f-a53c-facffbf8db4a
-- title:
--   Global Theory: exists tuple normalisation charts
-- statement:
--   The Global Theory construction uses the exists tuple normalisation charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L190-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L190-L260

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

theorem GlobalTheory.exists_tuple_normalisation_charts (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    [IsDedekindDomain o] [CharZero Ω] (_hinj : Function.Injective (algebraMap o Ω)) (J : Type)
    [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e ∧ (∀ i, ∃ k, z k = t i ^ e) ∧
      (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔
        IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k),
        ∑ i, (c i : Ω) * (t i ^ e / z k) = 1 := by sorry
