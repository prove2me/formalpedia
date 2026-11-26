-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_residual_exact
-- name    : Kyprianou.Ch04.ito43_cosine_residual_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:49.528006+00:00
-- url     : https://prove2.me/theorems/d94a8381-2b87-4222-ad65-d86afafcaf7c
-- title:
--   Cosine residual equals Gaussian minus grid cosine sum plus jump cosine integral
-- statement:
--   On each common cadlag path with square-summable jumps the quadratic and cosine marks are integrable. Subtract their integrals and finite sums; the integral of one over the time interval is its length.
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
open Set

theorem Kyprianou.Ch04.ito43_cosine_residual_exact {Omega : Type} [MeasurableSpace Omega]
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
          (nhds (Xleft t omega))) :
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
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let G : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ) -
        ∑ k ∈ Finset.range n, q m (X (v (k+1)) w-X (v k) w)
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    ∀ᵐ w ∂P, ∀ m n t, t ≤ T → B m n t w = G m n t w+J m t w := by sorry
