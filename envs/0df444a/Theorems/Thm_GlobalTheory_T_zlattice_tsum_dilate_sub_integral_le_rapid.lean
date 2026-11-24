-- Prove2me | Theorems.Thm_GlobalTheory_T_zlattice_tsum_dilate_sub_integral_le_rapid
-- name    : GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:00:59.696254+00:00
-- url     : https://prove2.me/theorems/0b896ca0-479b-41cd-b87e-b29f9508142e
-- title:
--   T: zlattice tsum dilate sub integral le rapid
-- statement:
--   The T construction uses the zlattice tsum dilate sub integral le rapid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ZlatticeTsumDilateSubIntegralLeRapidStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ZlatticeTsumDilateSubIntegralLeRapidStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapidStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) / ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by sorry
