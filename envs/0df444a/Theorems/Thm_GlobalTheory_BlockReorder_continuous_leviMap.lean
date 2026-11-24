-- Prove2me | Theorems.Thm_GlobalTheory_BlockReorder_continuous_leviMap
-- name    : GlobalTheory.BlockReorder.continuous_leviMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:45.820264+00:00
-- url     : https://prove2.me/theorems/93bb096c-eab9-4ea0-a813-ebb721d01fec
-- title:
--   Block Reorder: continuous levi Map
-- statement:
--   The Block Reorder construction uses the continuous levi Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L120-L130

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

theorem GlobalTheory.BlockReorder.continuous_leviMap [TopologicalSpace R] [IsTopologicalRing R] (e : (Σ a, m a) ≃ n) :
    Continuous (leviMap R e) := by sorry
