-- Prove2me | Theorems.Thm_GlobalTheory_ZeroBand_band_le
-- name    : GlobalTheory.ZeroBand.band_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:35.711233+00:00
-- url     : https://prove2.me/theorems/e3e42e49-7be1-46c8-8a9d-73f923f4d5b2
-- title:
--   Zero Band: band le
-- statement:
--   The Zero Band construction uses the band le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteBox.lean#L35-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteBox.lean#L35-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroBand

theorem GlobalTheory.ZeroBand.band_le (f : ℂ → ℂ) (m : ℂ → ℕ) (B : ℝ → ℝ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}, (m ρ : ℝ) ≤ B t)
    {u T T' : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (B T + B (-T)) * (u / T) := by sorry
