-- Prove2me | Theorems.Thm_GlobalTheory_BlockReorder_hasFiniteLength_parInd
-- name    : GlobalTheory.BlockReorder.hasFiniteLength_parInd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:40.901949+00:00
-- url     : https://prove2.me/theorems/46f6f98c-c513-4fb6-92e8-49f2ed253ae2
-- title:
--   Block Reorder: has Finite Length par Ind
-- statement:
--   The Block Reorder construction uses the has Finite Length par Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L238-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean#L238-L245

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.BlockReorder.hasFiniteLength_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (h : HasFiniteLength (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)))) :
    HasFiniteLength (parInd e ρ) := by sorry
