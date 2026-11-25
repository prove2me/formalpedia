-- Prove2me | Theorems.Thm_GlobalTheory_HlCoc_main
-- name    : GlobalTheory.HlCoc.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:13.03432+00:00
-- url     : https://prove2.me/theorems/9051f4e2-8544-47fb-80c9-d853678d3153
-- title:
--   Hl Coc: main
-- statement:
--   The Hl Coc construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L150-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L150-L354

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

theorem GlobalTheory.HlCoc.main (l : ℕ) [Fact l.Prime] [CompactSpace G] [T2Space G] [T2Space M]
    (T : AddSubgroup M) (hT : IsCompact (T : Set M)) (hTs : ∀ g : G, ∀ t ∈ T, g • t ∈ T)
    (hTl : ∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U)
    (lam : G →* Multiplicative ℤ_[l]) (g₀ : G) (hlam : Continuous lam)
    (hg₀ : lam g₀ = Multiplicative.ofAdd 1) (b z : M)
    (hH : ∀ h, lam h = 1 → h • z = z ∧ h • b - b ∈ T) (hz : z - (g₀ • b - b) ∈ T) :
    ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + g • c h) ∧
      (∀ h, lam h = 1 → c h = -(h • b - b)) ∧
      ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b) := by sorry
