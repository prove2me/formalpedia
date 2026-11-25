-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_rowSub_mem_inv
-- name    : GlobalTheory.MinorFrame.rowSub_mem_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:07.994307+00:00
-- url     : https://prove2.me/theorems/d11ae0f0-eb1a-5021-bfb2-a46941965370
-- title:
--   Minor Frame: row Sub mem inv
-- statement:
--   The Minor Frame construction uses the row Sub mem inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L84-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by sorry
