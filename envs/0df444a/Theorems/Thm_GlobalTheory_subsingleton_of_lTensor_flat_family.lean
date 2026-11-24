-- Prove2me | Theorems.Thm_GlobalTheory_subsingleton_of_lTensor_flat_family
-- name    : GlobalTheory.subsingleton_of_lTensor_flat_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:21.55284+00:00
-- url     : https://prove2.me/theorems/55aac011-77fb-4b2f-9845-453d1789a946
-- title:
--   Global Theory: subsingleton of l Tensor flat family
-- statement:
--   The Global Theory construction uses the subsingleton of l Tensor flat family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamily.lean#L6-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamily.lean#L6-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by sorry
