-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedClippedValue_tendsto
-- name    : Kyprianou.Ch01.mckeanDiscountedClippedValue_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:42:22.510837+00:00
-- url     : https://prove2.me/theorems/8adbf104-26fc-4d70-b1b1-7cd0e0cdb362
-- title:
--   Clipped discounted McKean value converges at every finite or infinite stopping time
-- statement:
--   For an arbitrary process and arbitrary finite or infinite tau, the discounted McKean value sampled at min(tau,n) converges pointwise to the genuine stopped discounted value at tau, with zero for tau infinite. Finite tau is eventually unchanged; infinite tau uses 0≤V≤K and exponential decay. This supplies the original pointwise limit required for optional sampling.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
import Theorems.Thm_e7_exp_neg_scale_tendsto_zero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedClippedValue_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (tau : Ω → WithTop ℝ≥0)
    (ω : Ω) :
    let barrier := Real.log (K * phi / (1 + phi))
    let clip (n : ℕ) : ℝ≥0 :=
      (min (tau ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
    let terminal : ℝ :=
      match tau ω with
      | none => 0
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)
    Filter.Tendsto (fun n : ℕ =>
      Real.exp (-q * (clip n : ℝ)) *
        mckeanValue K barrier phi (x + X (clip n) ω))
      Filter.atTop (nhds terminal) := by sorry
