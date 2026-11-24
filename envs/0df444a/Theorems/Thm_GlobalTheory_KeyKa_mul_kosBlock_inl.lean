-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_mul_kosBlock_inl
-- name    : GlobalTheory.KeyKa.mul_kosBlock_inl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:19.646806+00:00
-- url     : https://prove2.me/theorems/26f687b3-d146-4d49-b535-c3a0399c46ef
-- title:
--   Key Ka: mul kos Block inl
-- statement:
--   The Key Ka construction uses the mul kos Block inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L109-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

theorem GlobalTheory.KeyKa.mul_kosBlock_inl (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (I : Finset (Fin g)) (a : Fin (N I.card)) (q : KIx g d N) :
    (D * kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) q (.inl ⟨I, a⟩) = ∑ c, D q (.inl ⟨I, c⟩) * C I.card c a := by sorry
