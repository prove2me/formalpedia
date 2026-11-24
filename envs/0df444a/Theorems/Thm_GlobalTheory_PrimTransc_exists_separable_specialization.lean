-- Prove2me | Theorems.Thm_GlobalTheory_PrimTransc_exists_separable_specialization
-- name    : GlobalTheory.PrimTransc.exists_separable_specialization
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:37.179966+00:00
-- url     : https://prove2.me/theorems/470fd48c-a799-4265-b1ce-910ebe29accd
-- title:
--   Prim Transc: exists separable specialization
-- statement:
--   The Prim Transc construction uses the exists separable specialization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecialization.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveMonicSeparableSpecialization.lean#L10-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open GlobalTheory GlobalTheory.PrimTransc

theorem GlobalTheory.PrimTransc.exists_separable_specialization {D : ℕ} (P : (MvPolynomial (Fin D) ℚ)[X])
    (h : (P.map (algebraMap (MvPolynomial (Fin D) ℚ) (FractionRing (MvPolynomial (Fin D) ℚ)))).Separable) :
    ∃ c : Fin D → ℚ, (P.map (MvPolynomial.eval c)).Separable := by sorry
