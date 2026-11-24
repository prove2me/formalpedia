-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_constantCoeff_rsub
-- name    : GlobalTheory.MinorFrame.constantCoeff_rsub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:33.307813+00:00
-- url     : https://prove2.me/theorems/73a5ae8e-324a-49e4-beb2-c26f43b36ba6
-- title:
--   Minor Frame: constant Coeff rsub
-- statement:
--   The Minor Frame construction uses the constant Coeff rsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L13-L19

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

theorem GlobalTheory.MinorFrame.constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by sorry
