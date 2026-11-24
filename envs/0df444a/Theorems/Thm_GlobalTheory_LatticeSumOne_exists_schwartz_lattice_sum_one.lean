-- Prove2me | Theorems.Thm_GlobalTheory_LatticeSumOne_exists_schwartz_lattice_sum_one
-- name    : GlobalTheory.LatticeSumOne.exists_schwartz_lattice_sum_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:30.977632+00:00
-- url     : https://prove2.me/theorems/a506f4b2-75ea-46ba-b719-3aad18070e20
-- title:
--   Lattice Sum One: exists schwartz lattice sum one
-- statement:
--   The Lattice Sum One construction uses the exists schwartz lattice sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L33-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L33-L86

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
open GlobalTheory GlobalTheory.LatticeSumOne
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.LatticeSumOne.exists_schwartz_lattice_sum_one (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by sorry
