-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnnihOpen_isOpen_annihilator_of_isCompact
-- name    : GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:30.368383+00:00
-- url     : https://prove2.me/theorems/9a1f2795-4d3a-452d-a69d-436ab6933baa
-- title:
--   Annih Open: is Open annihilator of is Compact
-- statement:
--   The Annih Open construction uses the is Open annihilator of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenCharacterAnnihilator.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenCharacterAnnihilator.lean#L8-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihOpen

theorem GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)),
      IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by sorry
