-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenArrivalScalesByJumpMass
-- name    : Kyprianou.Ch01.frozenArrivalScalesByJumpMass
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T20:54:50.79654+00:00
-- url     : https://prove2.me/theorems/0b84743d-268b-4027-b124-5f687374fdaa
-- title:
--   Frozen arrival scales by the jump mass
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted sequences. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The intersection of $\{M=j-1\}$ with
--   $$\{A\le yt\}\cap\{Y^{y-1+j}_{t-A/y}=k\}$$
--   has probability equal to
--   $$\nu(\{j-1\})\int_{(-\infty,yt]}\mathbb{Q}\big(Y^{y-1+j}_{t-a/y}=k\big)\,d\operatorname{Exp}(\lambda)(a).$$
--   The jump mass is constant along the arrival line. The integral is the law of the population frozen at the deterministic time $t-a/y$.
-- source:
--   Kyprianou (2006), Section 1.3.4; independence scales the frozen arrival integral by the jump mass.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenArrivalScalesByJumpMass
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
      (∫ a in Iic ((y : ℝ) * (t : ℝ)),
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k}).toReal
        ∂expMeasure (rate : ℝ)) *
        (jumpLaw {((j : ℝ) - 1)}).toReal := by
  sorry
