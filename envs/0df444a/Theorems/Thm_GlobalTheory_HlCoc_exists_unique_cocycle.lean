-- Prove2me | Theorems.Thm_GlobalTheory_HlCoc_exists_unique_cocycle
-- name    : GlobalTheory.HlCoc.exists_unique_cocycle
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:19.382639+00:00
-- url     : https://prove2.me/theorems/156c7441-5a26-457c-a8d0-46f24080e1ed
-- title:
--   Hl Coc: exists unique cocycle
-- statement:
--   The Hl Coc construction uses the exists unique cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L356-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L356-L365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
variable [TopologicalSpace G] [TopologicalSpace M]
variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]

theorem GlobalTheory.HlCoc.exists_unique_cocycle : ∀ (l : ℕ) [Fact l.Prime] (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] (a : G → (M →+ M)), (∀ x, a 1 x = x) → (∀ g h x, a (g * h) x = a g (a h x)) → Continuous (fun p : G × M => a p.1 p.2) → ∀ T : AddSubgroup M, IsCompact (T : Set M) → (∀ g, ∀ t ∈ T, a g t ∈ T) → (∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U) → ∀ (lam : G →* Multiplicative ℤ_[l]) (g₀ : G), Continuous lam → lam g₀ = Multiplicative.ofAdd 1 → ∀ b z : M, (∀ h, lam h = 1 → a h z = z ∧ a h b - b ∈ T) → z - (a g₀ b - b) ∈ T → ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + a g (c h)) ∧ (∀ h, lam h = 1 → c h = -(a h b - b)) ∧ ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (a g b - b) := by sorry
