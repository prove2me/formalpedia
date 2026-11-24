-- Prove2me | Theorems.Thm_GlobalTheory_JacquetBlocks_mem_unipRad_iff_blk
-- name    : GlobalTheory.JacquetBlocks.mem_unipRad_iff_blk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:33.0113+00:00
-- url     : https://prove2.me/theorems/13876821-41e9-4c2f-9b9a-565f5a8679ea
-- title:
--   Jacquet Blocks: mem unip Rad iff blk
-- statement:
--   The Jacquet Blocks construction uses the mem unip Rad iff blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L48-L60

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.JacquetBlocks.mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by sorry
