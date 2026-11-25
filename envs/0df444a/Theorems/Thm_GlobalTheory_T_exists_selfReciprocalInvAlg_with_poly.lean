-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_selfReciprocalInvAlg_with_poly
-- name    : GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:15.379202+00:00
-- url     : https://prove2.me/theorems/6660bcb9-9dcd-4120-a6a5-05f16881d872
-- title:
--   T: exists self Reciprocal Inv Alg with poly
-- statement:
--   The T construction uses the exists self Reciprocal Inv Alg with poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPolyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPolyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by sorry
