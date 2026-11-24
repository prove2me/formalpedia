-- Prove2me | Theorems.Thm_GlobalTheory_LatticeSumOne_exists_radius
-- name    : GlobalTheory.LatticeSumOne.exists_radius
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:40.719427+00:00
-- url     : https://prove2.me/theorems/30a028dc-08be-4284-9f0b-d3d65c0cdeca
-- title:
--   Lattice Sum One: exists radius
-- statement:
--   The Lattice Sum One construction uses the exists radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzPartitionOfUnityLattice.lean#L9-L31

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

theorem GlobalTheory.LatticeSumOne.exists_radius (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ R : ℝ, ∀ x : V, ∃ l : Λ, ‖x + l‖ ≤ R := by sorry
