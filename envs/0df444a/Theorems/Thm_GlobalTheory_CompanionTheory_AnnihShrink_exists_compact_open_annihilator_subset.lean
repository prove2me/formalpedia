-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_exists_compact_open_annihilator_subset
-- name    : GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:28.418016+00:00
-- url     : https://prove2.me/theorems/378759a4-4258-4b35-8088-e1f6b55cf991
-- title:
--   Annih Shrink: exists compact open annihilator subset
-- statement:
--   The Annih Shrink construction uses the exists compact open annihilator subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L51-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L51-L101

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihShrink
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)),
      U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k),
        IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧
        {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by sorry
