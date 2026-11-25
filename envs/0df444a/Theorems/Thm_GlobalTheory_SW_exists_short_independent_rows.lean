-- Prove2me | Theorems.Thm_GlobalTheory_SW_exists_short_independent_rows
-- name    : GlobalTheory.SW.exists_short_independent_rows
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:14.373238+00:00
-- url     : https://prove2.me/theorems/935bcad1-96fd-4c53-8642-61de36c25d8b
-- title:
--   SW: exists short independent rows
-- statement:
--   The SW construction uses the exists short independent rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L187-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L187-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.exists_short_independent_rows :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ →
      ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin N) m E),
        LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin N) (Fin N) E, IntM a ∧ a.det ≠ 0 ∧
          ∏ i, (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * W) i j)‖ ^ 2) ^ Ψ.card ≤
            C * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re := by sorry
