-- Prove2me | Theorems.Thm_GlobalTheory_summable_norm_coset_out
-- name    : GlobalTheory.summable_norm_coset_out
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:42.197722+00:00
-- url     : https://prove2.me/theorems/bbcf5ddd-1031-46a9-8c8e-c6e3a3aa7d69
-- title:
--   Global Theory: summable norm coset out
-- statement:
--   The Global Theory construction uses the summable norm coset out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNormCosetOut.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNormCosetOut.lean#L6-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNormCosetOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by sorry
