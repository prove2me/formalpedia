-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Burnside_mem_of_irred
-- name    : GlobalTheory.CompanionTheory.Burnside.mem_of_irred
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:07.913503+00:00
-- url     : https://prove2.me/theorems/bceecec1-53f4-4f21-b2e7-09880987fbf3
-- title:
--   Burnside: mem of irred
-- statement:
--   The Burnside construction uses the mem of irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BurnsideSurjOfIrred.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BurnsideSurjOfIrred.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Burnside

theorem GlobalTheory.CompanionTheory.Burnside.mem_of_irred {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by sorry
