-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_sum_dilate_haar_asymptotic
-- name    : GlobalTheory.T.lattice_sum_dilate_haar_asymptotic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:51.329953+00:00
-- url     : https://prove2.me/theorems/abce8acb-0cb7-4620-9e37-d0095312abad
-- title:
--   T: lattice sum dilate haar asymptotic
-- statement:
--   The T construction uses the lattice sum dilate haar asymptotic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LatticeSumDilateHaarAsymptoticStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LatticeSumDilateHaarAsymptoticStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptotic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
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

theorem GlobalTheory.T.lattice_sum_dilate_haar_asymptotic : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by sorry
