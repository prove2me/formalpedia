-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalLattice_coe_ballSubgroup
-- name    : GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:08.234506+00:00
-- url     : https://prove2.me/theorems/6e8acbbf-2110-45e7-b098-9310bdd116f4
-- title:
--   Local Lattice: coe ball Subgroup
-- statement:
--   The Local Lattice construction uses the coe ball Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContaining.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContaining.lean#L22-L27

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

theorem GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by sorry
