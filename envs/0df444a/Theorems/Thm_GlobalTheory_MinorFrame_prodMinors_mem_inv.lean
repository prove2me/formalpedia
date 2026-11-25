-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_prodMinors_mem_inv
-- name    : GlobalTheory.MinorFrame.prodMinors_mem_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:41.109831+00:00
-- url     : https://prove2.me/theorems/a01513fd-5826-5c51-85d6-a4c475491e68
-- title:
--   Minor Frame: prod Minors mem inv
-- statement:
--   The Minor Frame construction uses the prod Minors mem inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L70-L71

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

theorem GlobalTheory.MinorFrame.prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n := by sorry
