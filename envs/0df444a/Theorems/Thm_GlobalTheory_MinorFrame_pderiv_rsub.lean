-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_pderiv_rsub
-- name    : GlobalTheory.MinorFrame.pderiv_rsub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:05.930045+00:00
-- url     : https://prove2.me/theorems/52463db1-52fa-4cb0-bc59-5cb5c2f601c7
-- title:
--   Minor Frame: pderiv rsub
-- statement:
--   The Minor Frame construction uses the pderiv rsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L21-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean#L21-L45

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

theorem GlobalTheory.MinorFrame.pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by sorry
