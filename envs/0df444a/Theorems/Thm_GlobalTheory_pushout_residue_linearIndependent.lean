-- Prove2me | Theorems.Thm_GlobalTheory_pushout_residue_linearIndependent
-- name    : GlobalTheory.pushout_residue_linearIndependent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:16.606144+00:00
-- url     : https://prove2.me/theorems/f80a6af8-746d-40ad-8495-25ca906c3fd9
-- title:
--   Global Theory: pushout residue linear Independent
-- statement:
--   The Global Theory construction uses the pushout residue linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PushoutResidueLinearIndependent.lean#L6-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PushoutResidueLinearIndependent.lean#L6-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PushoutResidueLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.pushout_residue_linearIndependent :
  ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by sorry
