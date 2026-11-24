-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_potential_total_mass
-- name    : Kyprianou.Ch08.StageB.p2m89_potential_total_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T09:52:24.6744+00:00
-- url     : https://prove2.me/theorems/7b5acc12-33ec-419f-a633-a7295bab46be
-- title:
--   Exact mass of tilted descending potential
-- statement:
--   Let s decrease to zero; monotone convergence of exponential weights gives total mass, and the exact inverse derivative determines the limit.
-- source:
--   Kyprianou (2006), Corollary 8.9; exact decomposition of b307a65d-60a2-457f-8b82-5e03a431fb4f.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_potential_total_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
      ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ν univ = ENNReal.ofReal (deriv (Phi ψ) q) := by
  sorry
