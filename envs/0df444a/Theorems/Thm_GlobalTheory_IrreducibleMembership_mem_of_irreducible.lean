-- Prove2me | Theorems.Thm_GlobalTheory_IrreducibleMembership_mem_of_irreducible
-- name    : GlobalTheory.IrreducibleMembership.mem_of_irreducible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:26.201801+00:00
-- url     : https://prove2.me/theorems/3ea1b531-b182-4730-a9aa-b24f35f59dda
-- title:
--   Irreducible Membership: mem of irreducible
-- statement:
--   The Irreducible Membership construction uses the mem of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemOfIrreducible.lean#L7-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemOfIrreducible.lean#L7-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IrreducibleMembership

theorem GlobalTheory.IrreducibleMembership.mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by sorry
