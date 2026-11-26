-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_high_frequency
-- name    : Kyprianou.Ch04.ito43_cosine_grid_high_frequency
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:32:30.615792+00:00
-- url     : https://prove2.me/theorems/fbaf30de-3458-4c7f-994f-774f343033c2
-- title:
--   Gaussian-centred stopped cosine grid has small high-frequency tail
-- statement:
--   Use independent bounded cosine deficits on the full deterministic grid. The characteristic exponent gives their exact mean; its normalised real part approaches the Gaussian coefficient. The maximal centred sum has variance at most twice the total mean divided by the frequency square. A clipped grid differs from a complete prefix in at most one bounded term.
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

theorem Kyprianou.Ch04.ito43_cosine_grid_high_frequency {Omega : Type} [MeasurableSpace Omega]
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
    let G : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ) -
        ∑ k ∈ Finset.range n, q m (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop, (P {w | ∃ t ≤ T, e ≤ |G m n t w|}).toReal ≤ η := by sorry
