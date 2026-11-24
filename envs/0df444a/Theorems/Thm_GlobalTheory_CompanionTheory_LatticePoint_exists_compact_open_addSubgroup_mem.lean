-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LatticePoint_exists_compact_open_addSubgroup_mem
-- name    : GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:48.838002+00:00
-- url     : https://prove2.me/theorems/a9747f8d-588b-4d09-8732-ed7e219ac5dc
-- title:
--   Lattice Point: exists compact open add Subgroup mem
-- statement:
--   The Lattice Point construction uses the exists compact open add Subgroup mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCompactOpenSubgroupMem.lean#L22-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCompactOpenSubgroupMem.lean#L22-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticePoint

theorem GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by sorry
