-- Prove2me | Theorems.Thm_GlobalTheory_exists_schwartz_hasCompactSupport_latticeTranslates_sum_one
-- name    : GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:03.919728+00:00
-- url     : https://prove2.me/theorems/f5cf3bf2-4574-4841-953e-3e44388da756
-- title:
--   Global Theory: exists schwartz has Compact Support lattice Translates sum one
-- statement:
--   The Global Theory construction uses the exists schwartz has Compact Support lattice Translates sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L92-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory

theorem GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by sorry
