-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_fockS_rsub_adj
-- name    : GlobalTheory.MinorFrame.fockS_rsub_adj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:51.055049+00:00
-- url     : https://prove2.me/theorems/63f353f6-995b-480d-8688-2ec9d77e0e64
-- title:
--   Minor Frame: fock S rsub adj
-- statement:
--   The Minor Frame construction uses the fock S rsub adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L64-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Formalism.L2.DIV
open GlobalTheory GlobalTheory.MinorFrame
variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem GlobalTheory.MinorFrame.fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by sorry
