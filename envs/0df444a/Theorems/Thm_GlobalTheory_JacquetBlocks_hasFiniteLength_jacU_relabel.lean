-- Prove2me | Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_jacU_relabel
-- name    : GlobalTheory.JacquetBlocks.hasFiniteLength_jacU_relabel
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:33.155314+00:00
-- url     : https://prove2.me/theorems/8f43f4e4-3d4b-48e8-921c-26925d8cb2bd
-- title:
--   Jacquet Blocks: has Finite Length jac U relabel
-- statement:
--   The Jacquet Blocks construction uses the has Finite Length jac U relabel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L159-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L159-L189

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.JacquetBlocks.hasFiniteLength_jacU_relabel (e : (Σ a, m a) ≃ n) (s : (Σ b, m' b) ≃ (Σ a, m a))
    (f : β → α) (hf : StrictMono f) (hs : ∀ x, (s x).1 = f x.1) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU (s.trans e) π)) : HasFiniteLength (jacU e π) := by sorry
