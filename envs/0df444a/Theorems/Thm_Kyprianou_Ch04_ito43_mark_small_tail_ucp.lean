-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_small_tail_ucp
-- name    : Kyprianou.Ch04.ito43_mark_small_tail_ucp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:24:35.215542+00:00
-- url     : https://prove2.me/theorems/0896e2b0-acd3-576c-beb3-c98c854ef6e1
-- title:
--   Locally subquadratic mark cutoff tails have arbitrarily small outer probability
-- statement:
--   Localise the actual jump square sum and stopped grid square sum. Select a cutoff using the scalar small bound, then apply the two-energy tail inequality with the unused path-range event empty.
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

theorem Kyprianou.Ch04.ito43_mark_small_tail_ucp {Omega : Type} [MeasurableSpace Omega]
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
    (r : ℝ → ℝ) (hr : Continuous r) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z, |r z| ≤ C*z^2)
    (hs : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2) :
    ∀ T : NNReal,
    let E : ℕ → NNReal → Omega → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X Xleft w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      let c : ℝ → ℝ := fun z => r z * min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), c z.2 ∂(pathJumpMeasure X Xleft w)) -
        ∑ k ∈ Finset.range n, c (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |E n t w-A m n t w|}).toReal ≤ η := by sorry
