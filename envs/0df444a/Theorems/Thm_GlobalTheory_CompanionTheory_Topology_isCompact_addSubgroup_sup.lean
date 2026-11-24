-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Topology_isCompact_addSubgroup_sup
-- name    : GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:27.135874+00:00
-- url     : https://prove2.me/theorems/e9a927bf-e138-4005-8aef-c0bb3e3375a6
-- title:
--   Topology: is Compact add Subgroup sup
-- statement:
--   The Topology construction uses the is Compact add Subgroup sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactSupAddSubgroup.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactSupAddSubgroup.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology

theorem GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by sorry
