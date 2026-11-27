-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_weighted_sup_envelope
-- name    : Kyprianou.Ch04.ito43_qv_weighted_sup_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:20.88072+00:00
-- url     : https://prove2.me/theorems/6e8629b2-2e58-5eaa-9b6e-b0ef289a2bbc
-- title:
--   Weighted quadratic variation error has a measurable bounded supremum
-- statement:
--   Use the square-summable jump series on the common cadlag event; weighted jump sums are limits of measurable finite cutoff sums. The time integral, weighted jump process and clipped grid sum have right-continuous bounded paths. Replace their error supremum by countably many times including the endpoint.
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

theorem Kyprianou.Ch04.ito43_qv_weighted_sup_envelope {Omega : Type} [MeasurableSpace Omega]
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
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :
    ∀ T : NNReal,
    let B : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      g (z.1,Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      g ((u k : ℝ), X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2)
    let C : ℕ → Omega → ℝ := fun n w =>
      sSup (Set.range (fun t : Set.Iic T => |B n t w|))
    (∀ n, AEStronglyMeasurable (C n) P) ∧
      ∀ᵐ w ∂P, ∀ n, BddAbove (Set.range (fun t : Set.Iic T => |B n t w|)) := by sorry
