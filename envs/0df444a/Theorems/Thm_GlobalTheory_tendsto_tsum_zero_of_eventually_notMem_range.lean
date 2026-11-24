-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_tsum_zero_of_eventually_notMem_range
-- name    : GlobalTheory.tendsto_tsum_zero_of_eventually_notMem_range
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:52.724368+00:00
-- url     : https://prove2.me/theorems/c95599cf-9517-4a1e-beec-1716f7fffb27
-- title:
--   Global Theory: tendsto tsum zero of eventually not Mem range
-- statement:
--   The Global Theory construction uses the tendsto tsum zero of eventually not Mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TendstoTsumZeroOfEventuallyNotMemRange.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TendstoTsumZeroOfEventuallyNotMemRange.lean#L22-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory

theorem GlobalTheory.tendsto_tsum_zero_of_eventually_notMem_range {K X Y : Type} [NontriviallyNormedField K]
    [IsUltrametricDist K] (τ : X → K) (hτ : Tendsto τ cofinite (𝓝 0)) (f : ℕ → Y → X)
    (hf : ∀ z, τ z ≠ 0 → ∀ᶠ j in atTop, ∀ μ, f j μ ≠ z) :
    Tendsto (fun j => ∑' μ, τ (f j μ)) atTop (𝓝 0) := by sorry
