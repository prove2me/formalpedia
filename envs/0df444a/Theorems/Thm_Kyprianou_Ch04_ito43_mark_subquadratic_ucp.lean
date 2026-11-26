-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_subquadratic_ucp
-- name    : Kyprianou.Ch04.ito43_mark_subquadratic_ucp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:23:31.558174+00:00
-- url     : https://prove2.me/theorems/dd266580-c6b1-4ce6-a9f5-66c166c94bc8
-- title:
--   Every continuous locally subquadratic mark satisfies stopped grid UCP convergence
-- statement:
--   Apply the general UCP approximation theorem with continuous cutoffs. The fixed cutoff convergence and two-energy small tail bound establish the result.
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

theorem Kyprianou.Ch04.ito43_mark_subquadratic_ucp {Omega : Type} [MeasurableSpace Omega]
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
    ∀ e : ℝ, 0 < e → Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by sorry
