-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_cutoff_measurable
-- name    : Kyprianou.Ch04.ito43_weighted_jump_cutoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:12:39.597557+00:00
-- url     : https://prove2.me/theorems/97f40e16-bf85-47f1-98e3-95d1708f8725
-- title:
--   Weighted jump integral with continuous cutoff is AE measurable
-- statement:
--   Use the deterministic stopped cutoff convergence at the fixed horizon. Every finite grid sum of the continuous cutoff kernel is AE measurable by coordinate measurability.
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

theorem Kyprianou.Ch04.ito43_weighted_jump_cutoff_measurable    {Omega : Type} [MeasurableSpace Omega]
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
    ∀ (t : NNReal) (m : ℕ), AEMeasurable (fun w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 *
          min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1))
          ∂(pathJumpMeasure X Xleft w)) P := by sorry
