-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IndexDuality_relIndex_annihilator_eq
-- name    : GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:48:11.358541+00:00
-- url     : https://prove2.me/theorems/6b0b50fe-b521-442f-91ce-01b1fdb19ef8
-- title:
--   Index Duality: rel Index annihilator eq
-- statement:
--   The Index Duality construction uses the rel Index annihilator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexAnnihilatorsDuality.lean#L88-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexAnnihilatorsDuality.lean#L88-L108

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDuality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IndexDuality

theorem GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) →
    IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) →
    (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by sorry
