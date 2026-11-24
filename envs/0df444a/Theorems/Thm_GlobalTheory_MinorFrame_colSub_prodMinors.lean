-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_colSub_prodMinors
-- name    : GlobalTheory.MinorFrame.colSub_prodMinors
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:26:32.919348+00:00
-- url     : https://prove2.me/theorems/60f808fc-ca0b-4a08-ab72-2db0cd946765
-- title:
--   Minor Frame: col Sub prod Minors
-- statement:
--   The Minor Frame construction uses the col Sub prod Minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L64-L68

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

theorem GlobalTheory.MinorFrame.colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by sorry
