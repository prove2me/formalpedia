-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_rsub_frameMat_of_mem_inv
-- name    : GlobalTheory.MinorFrame.rsub_frameMat_of_mem_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:48.526531+00:00
-- url     : https://prove2.me/theorems/fb6ee3b0-b451-4fab-a794-416f38c5b581
-- title:
--   Minor Frame: rsub frame Mat of mem inv
-- statement:
--   The Minor Frame construction uses the rsub frame Mat of mem inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinors.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinors.lean#L36-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDenseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by sorry
