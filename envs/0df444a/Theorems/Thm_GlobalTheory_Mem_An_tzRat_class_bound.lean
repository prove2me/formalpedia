-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_tzRat_class_bound
-- name    : GlobalTheory.Mem.An.tzRat_class_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:22.417249+00:00
-- url     : https://prove2.me/theorems/7eb2667a-894d-4333-947f-11d3f5998776
-- title:
--   An: tz Rat class bound
-- statement:
--   The An construction uses the tz Rat class bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L10-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L10-L84

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An

theorem GlobalTheory.Mem.An.tzRat_class_bound (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧
      ∀ (M b : ℕ) (B : ℝ), 3 ≤ M → M % 4 ≠ 2 → Nat.Coprime b M → (M : ℝ) ≤ B →
        ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
          (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) ∧
          ∀ Y : ℝ, B ^ C₀ ≤ Y →
            |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
              - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y := by sorry
