-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_grid_sum_measurable
-- name    : Kyprianou.Ch04.ito43_weighted_grid_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:53:51.302365+00:00
-- url     : https://prove2.me/theorems/ff985ddb-b6d2-470d-af36-c43eb276f607
-- title:
--   Weighted clipped grid sum has measurable sections
-- statement:
--   Use the proved coordinate AE measurability and continuity of the weight with its deterministic nonnegative time. Finite sums, differences and products preserve AE measurability.
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

theorem Kyprianou.Ch04.ito43_weighted_grid_sum_measurable   {Omega : Type} [MeasurableSpace Omega]
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
    ∀ (T : NNReal) (n : ℕ) (t : NNReal),
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      AEMeasurable (fun w => ∑ k ∈ Finset.range n,
        g ((u k:ℝ),X (u k) w)*(X (v (k+1)) w-X (v k) w)^2/2) P := by sorry
