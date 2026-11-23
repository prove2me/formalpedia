-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenPopulationScalesByJumpAtom
-- name    : Kyprianou.Ch01.frozenPopulationScalesByJumpAtom
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T20:01:27.124603+00:00
-- url     : https://prove2.me/theorems/52435b52-fa59-4af8-b81a-fb30896c0d8b
-- title:
--   Frozen population integral scales by the jump atom
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted sequences. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The atom
--   $$\{M=j-1\}\cap\{Y^{y-1+j}_{t-A/y}=k\}\cap\{A\le yt\}$$
--   has probability equal to
--   $$\nu(\{j-1\})\int_{(-\infty,yt]}\mathbb{Q}\big(Y^{y-1+j}_{t-a/y}=k\big)\,d\operatorname{Exp}(\lambda)(a).$$
--   The integrand is the probability of the shifted population at the deterministic residual time $t-a/y$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the frozen half-line integral factors through the mark atom.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenPopulationScalesByJumpAtom
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
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)}).toReal =
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
