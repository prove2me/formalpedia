-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_integral_measurable
-- name    : Kyprianou.Ch04.ito43_weighted_jump_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:53:44.588037+00:00
-- url     : https://prove2.me/theorems/1f870505-ebd6-5c1f-b444-e9bed0e3732c
-- title:
--   Weighted actual jump integral has measurable time sections
-- statement:
--   Use continuous mark cutoffs. At each cutoff the finite jump sum is the pathwise limit of measurable stopped grid sums by the proved deterministic cutoff theorem. Remove the cutoff using dominated convergence on the common finite squared-jump-energy event.
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

theorem Kyprianou.Ch04.ito43_weighted_jump_integral_measurable   {Omega : Type} [MeasurableSpace Omega]
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
    ∀ t : NNReal, AEMeasurable (fun w =>
      ∫ z in Set.Icc (0:ℝ) (t:ℝ) ×ˢ (Set.univ : Set ℝ),
        g (z.1,Xleft (Real.toNNReal z.1) w)*z.2^2/2
          ∂(pathJumpMeasure X Xleft w)) P := by sorry
