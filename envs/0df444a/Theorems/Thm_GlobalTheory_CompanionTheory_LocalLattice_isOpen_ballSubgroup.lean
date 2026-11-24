-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalLattice_isOpen_ballSubgroup
-- name    : GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:02.960691+00:00
-- url     : https://prove2.me/theorems/03adf139-f1e5-464f-92bb-ce98242dd3d6
-- title:
--   Local Lattice: is Open ball Subgroup
-- statement:
--   The Local Lattice construction uses the is Open ball Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContaining.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContaining.lean#L34-L40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalLattice
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by sorry
