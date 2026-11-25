-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_schwartz_partition_of_unity_lattice
-- name    : GlobalTheory.T.exists_schwartz_partition_of_unity_lattice
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:00.374795+00:00
-- url     : https://prove2.me/theorems/75b33162-45b6-494b-bec3-4af6391722b2
-- title:
--   T: exists schwartz partition of unity lattice
-- statement:
--   The T construction uses the exists schwartz partition of unity lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLatticeStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLatticeStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_schwartz_partition_of_unity_lattice : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by sorry
