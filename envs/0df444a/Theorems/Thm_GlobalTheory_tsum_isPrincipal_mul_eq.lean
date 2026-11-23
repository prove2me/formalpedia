-- Prove2me | Theorems.Thm_GlobalTheory_tsum_isPrincipal_mul_eq
-- name    : GlobalTheory.tsum_isPrincipal_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:43.258149+00:00
-- url     : https://prove2.me/theorems/e6252063-365b-4380-b156-0cf753daf168
-- title:
--   Global Theory: tsum is Principal mul eq
-- statement:
--   The Global Theory construction uses the tsum is Principal mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealEqSumClassGroup.lean#L30-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealEqSumClassGroup.lean#L30-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.tsum_isPrincipal_mul_eq {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (F : Ideal (𝓞 K) → ℂ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal}, F (I * B) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, F J := by sorry
