-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_colSub_minorAt
-- name    : GlobalTheory.MinorFrame.colSub_minorAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:26:36.408412+00:00
-- url     : https://prove2.me/theorems/69385e0a-ac22-44fe-9dd0-d39e381d6222
-- title:
--   Minor Frame: col Sub minor At
-- statement:
--   The Minor Frame construction uses the col Sub minor At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L54-L62

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

theorem GlobalTheory.MinorFrame.colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by sorry
