-- Prove2me | Theorems.Thm_GlobalTheory_TwistTie_det_sub_mem_of_conj
-- name    : GlobalTheory.TwistTie.det_sub_mem_of_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:41.497933+00:00
-- url     : https://prove2.me/theorems/407e3664-0a7c-4a34-8332-fd14c2a98007
-- title:
--   Twist Tie: det sub mem of conj
-- statement:
--   The Twist Tie construction uses the det sub mem of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DetSubMemOfConj.lean#L61-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DetSubMemOfConj.lean#L61-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem GlobalTheory.TwistTie.det_sub_mem_of_conj {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (A : Subring R) (hf : ∀ x, f x ∈ A)
    (I : Ideal O) (J : AddSubgroup R) (hJ : ∀ x ∈ I, ∀ y ∈ A, f x * y ∈ J) {n : ℕ} (G P Y : Matrix (Fin n) (Fin n) R)
    (a : Matrix (Fin n) (Fin n) O) (t m : O) (ht : t - 1 ∈ I) (hm : m ∈ I) (hP : IsUnit P.det) (hG : G.det ∈ A)
    (hY : ∀ i j, Y i j ∈ A) (h : (f t • G) * P = P * (a.map f + f m • Y)) : G.det - f a.det ∈ J := by sorry
