-- Prove2me | Theorems.Thm_GlobalTheory_BlockReorder_leviMap_surjective
-- name    : GlobalTheory.BlockReorder.leviMap_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:02:36.679074+00:00
-- url     : https://prove2.me/theorems/c83a89ae-b319-4ac8-994d-c3c4f4d9051c
-- title:
--   Block Reorder: levi Map surjective
-- statement:
--   The Block Reorder construction uses the levi Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L104-L109

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
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}

theorem GlobalTheory.BlockReorder.leviMap_surjective (e : (Σ a, m a) ≃ n) : Function.Surjective (leviMap R e) := by sorry
