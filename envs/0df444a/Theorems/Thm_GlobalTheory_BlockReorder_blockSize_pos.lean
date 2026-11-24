-- Prove2me | Theorems.Thm_GlobalTheory_BlockReorder_blockSize_pos
-- name    : GlobalTheory.BlockReorder.blockSize_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:35.77711+00:00
-- url     : https://prove2.me/theorems/8ca6d41a-ac35-443f-92de-309c9ece1340
-- title:
--   Block Reorder: block Size pos
-- statement:
--   The Block Reorder construction uses the block Size pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L24-L24

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.BlockReorder.blockSize_pos (i : Fin (numBlocks m)) : 0 < blockSize m i := by sorry
