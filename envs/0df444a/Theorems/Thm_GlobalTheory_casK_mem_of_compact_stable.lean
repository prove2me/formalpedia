-- Prove2me | Theorems.Thm_GlobalTheory_casK_mem_of_compact_stable
-- name    : GlobalTheory.casK_mem_of_compact_stable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:20.673747+00:00
-- url     : https://prove2.me/theorems/02256ae4-971c-409c-83eb-77c27ff420c9
-- title:
--   Global Theory: cas K mem of compact stable
-- statement:
--   The Global Theory construction uses the cas K mem of compact stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeSubspaceMonotone.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeSubspaceMonotone.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.casK_mem_of_compact_stable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) : ∀ x ∈ S, CasK ε E x ∈ S := by sorry
