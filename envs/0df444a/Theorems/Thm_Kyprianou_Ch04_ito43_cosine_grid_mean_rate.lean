-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_mean_rate
-- name    : Kyprianou.Ch04.ito43_cosine_grid_mean_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:45:05.765817+00:00
-- url     : https://prove2.me/theorems/83704cd0-7529-4fb6-bb2d-549d06a4132c
-- title:
--   Normalised cosine increment mean has Gaussian rate at high frequency
-- statement:
--   Take the small mesh limit in the exact increment mean, then use the proved normalised exponent limit.
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

theorem Kyprianou.Ch04.ito43_cosine_grid_mean_rate  {Omega : Type} [MeasurableSpace Omega]
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
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let μ : ℕ → ℕ → ℝ := fun m n =>
      ∫ w, q m (X (T/(n:NNReal)) w) ∂P
    ∀ e : ℝ, 0 < e → ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      |(n:ℝ)*μ m n-((triplet.gaussianVariance:ℝ)/2)*(T:ℝ)| < e := by sorry
