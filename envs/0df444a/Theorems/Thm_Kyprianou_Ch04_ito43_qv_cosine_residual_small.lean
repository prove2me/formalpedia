-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_residual_small
-- name    : Kyprianou.Ch04.ito43_qv_cosine_residual_small
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:53:26.045673+00:00
-- url     : https://prove2.me/theorems/345e4dd1-9b66-4f0e-8c58-7ce9b6ec139d
-- title:
--   High-frequency cosine residual is small uniformly in probability
-- statement:
--   On the common finite jump energy event the residual equals the Gaussian clock plus the cosine jump sum minus the stopped cosine grid sum. The jump sum vanishes at high frequency by dominated convergence. The cosine grid has mean approaching the Gaussian clock and vanishing maximal fluctuations by the bounded increment square estimate and independent increments.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

theorem Kyprianou.Ch04.ito43_qv_cosine_residual_small {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    :
    ∀ T : NNReal,
    let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      (X (v (k+1)) omega - X (v k) omega)^2 / 2)
    let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t omega =>
      let a : ℝ := (m:ℝ)+1
      let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
        r z.2 ∂(pathJumpMeasure X Xleft omega)) -
      (∑ k ∈ Finset.range n, r (X (v (k+1)) omega-X (v k) omega))
    let B : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w => E n t w-A m n t w
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |B m n t w|}).toReal ≤ η := by sorry
