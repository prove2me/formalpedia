-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_volume_near_le
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.volume_near_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:17.998533+00:00
-- url     : https://prove2.me/theorems/4e21a467-fe3a-484e-af25-1719529f4a1b
-- title:
--   Real Tail: volume near le
-- statement:
--   The Real Tail construction uses the volume near le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L98-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L98-L139

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.volume_near_le {a : ℕ} {Q : (P → ι → ℝ) → (P → ℝ)} {C : ℝ≥0}
    (hbox : ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (v : P) {U : Set (P → ℝ)} (hU : MeasurableSet U)
    (j : ℕ) :
    (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a * Fintype.card P)) := by sorry
