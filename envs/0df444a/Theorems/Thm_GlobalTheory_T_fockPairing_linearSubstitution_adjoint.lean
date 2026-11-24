-- Prove2me | Theorems.Thm_GlobalTheory_T_fockPairing_linearSubstitution_adjoint
-- name    : GlobalTheory.T.fockPairing_linearSubstitution_adjoint
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:57.259873+00:00
-- url     : https://prove2.me/theorems/ac1a7801-fc75-4ecc-afcc-a71ce5e4a727
-- title:
--   T: fock Pairing linear Substitution adjoint
-- statement:
--   The T construction uses the fock Pairing linear Substitution adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjointStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjointStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fockPairing_linearSubstitution_adjoint : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' = Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by sorry
