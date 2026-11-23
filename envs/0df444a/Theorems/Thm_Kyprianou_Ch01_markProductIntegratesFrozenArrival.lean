-- Prove2me | Theorems.Thm_Kyprianou_Ch01_markProductIntegratesFrozenArrival
-- name    : Kyprianou.Ch01.markProductIntegratesFrozenArrival
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T20:26:22.610091+00:00
-- url     : https://prove2.me/theorems/09c67292-0893-496d-8cfd-0237f03bec6e
-- title:
--   Mark product integrates the frozen arrival
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted sequences. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The intersection of $\{M=j-1\}$ with
--   $$\{A\le yt\}\cap\{Y^{y-1+j}_{t-A/y}=k\}$$
--   has probability equal to
--   $$\int_{(-\infty,yt]}\Big(\mathbb{Q}\big(Y^{y-1+j}_{t-a/y}=k\big)\cdot\mathbb{Q}(M=j-1)\Big)\,d\operatorname{Exp}(\lambda)(a),$$
--   where the product of the two probabilities is formed in the extended nonnegative reals and then read as a real number.
-- source:
--   Kyprianou (2006), Section 1.3.4; the frozen arrival integral carries the product of the mark and population probabilities.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.markProductIntegratesFrozenArrival
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    (Q ({ω | marks 0 ω = (j : ℝ) - 1} ∩
        {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) + j)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          arrival 0 ω ≤ (y : ℝ) * (t : ℝ)})).toReal =
      ∫ a in Iic ((y : ℝ) * (t : ℝ)),
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k} *
          Q {ω | marks 0 ω = (j : ℝ) - 1}).toReal
        ∂expMeasure (rate : ℝ) := by
  sorry
