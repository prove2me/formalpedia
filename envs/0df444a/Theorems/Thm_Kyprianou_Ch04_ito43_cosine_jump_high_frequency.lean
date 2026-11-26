-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_jump_high_frequency
-- name    : Kyprianou.Ch04.ito43_cosine_jump_high_frequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:40.862133+00:00
-- url     : https://prove2.me/theorems/84bde259-b9c1-47ee-8103-8401043e309b
-- title:
--   Actual jump cosine deficit uniformly vanishes at high frequencies
-- statement:
--   On the common cadlag and square-summable jump event, dominated convergence gives vanishing total jump cosine integral. The full horizon bounds every shorter horizon because the cosine deficit is nonnegative. Obtain measurable versions via the mark-only Borel jump-series theorem.
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

theorem Kyprianou.Ch04.ito43_cosine_jump_high_frequency {Omega : Type} [MeasurableSpace Omega]
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
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      (P {w | ∃ t ≤ T, e ≤ |J m t w|}).toReal ≤ η := by sorry
