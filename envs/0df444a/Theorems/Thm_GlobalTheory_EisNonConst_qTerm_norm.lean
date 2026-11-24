-- Prove2me | Theorems.Thm_GlobalTheory_EisNonConst_qTerm_norm
-- name    : GlobalTheory.EisNonConst.qTerm_norm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:59:06.662648+00:00
-- url     : https://prove2.me/theorems/5fc81472-1f61-4c0a-bbbb-e3e3c0061f3e
-- title:
--   Eis Non Const: q Term norm
-- statement:
--   The Eis Non Const construction uses the q Term norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSum.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSum.lean#L15-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

theorem GlobalTheory.EisNonConst.qTerm_norm {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    ((‖qTerm 𝔞 k z p‖ : ℝ) : ℂ) = qTerm 𝔞 k (fun τ => Complex.I * ((z τ).im : ℂ)) p := by sorry
