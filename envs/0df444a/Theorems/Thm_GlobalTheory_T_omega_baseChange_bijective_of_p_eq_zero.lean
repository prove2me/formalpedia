-- Prove2me | Theorems.Thm_GlobalTheory_T_omega_baseChange_bijective_of_p_eq_zero
-- name    : GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:31.833905+00:00
-- url     : https://prove2.me/theorems/34d05232-1dce-464e-a071-6322078aa943
-- title:
--   T: omega base Change bijective of p eq zero
-- statement:
--   The T construction uses the omega base Change bijective of p eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R'], (p : R) = 0 → Function.Bijective (liftSemi (G.toBase R').omega) := by sorry
