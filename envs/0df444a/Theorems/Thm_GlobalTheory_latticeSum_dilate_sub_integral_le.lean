-- Prove2me | Theorems.Thm_GlobalTheory_latticeSum_dilate_sub_integral_le
-- name    : GlobalTheory.latticeSum_dilate_sub_integral_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:27.72214+00:00
-- url     : https://prove2.me/theorems/0545e251-338d-4801-a669-f30c9903f4cb
-- title:
--   Global Theory: lattice Sum dilate sub integral le
-- statement:
--   The Global Theory construction uses the lattice Sum dilate sub integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ZlatticeTsumDilateSubIntegralLeRapid.lean#L24-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ZlatticeTsumDilateSubIntegralLeRapid.lean#L24-L88

import Mathlib
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapid
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
open scoped FourierTransform RealInnerProductSpace SchwartzMap
open GlobalTheory

theorem GlobalTheory.latticeSum_dilate_sub_integral_le (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by sorry
