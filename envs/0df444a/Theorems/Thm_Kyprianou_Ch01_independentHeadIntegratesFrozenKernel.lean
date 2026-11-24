-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentHeadIntegratesFrozenKernel
-- name    : Kyprianou.Ch01.independentHeadIntegratesFrozenKernel
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:38:52.99184+00:00
-- url     : https://prove2.me/theorems/4b227c0f-7a3e-46a1-860e-dca2182fb39b
-- title:
--   Independent head integrates the unconditional frozen kernel
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, independent of the shifted sequences. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The conjoined event
--   $$\{M=j-1\}\cap\{A\le yt\}\cap\{Y^{y-1+j}_{t-A/y}=k\}$$
--   has probability equal to the integral, over $\{M=j-1\}\cap\{A\le yt\}$, of the unconditional probability $\mathbb{Q}(Y^{y-1+j}_{t-A/y}=k)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the head pushforward integral is a preimage integral of the frozen kernel.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentHeadIntegratesFrozenKernel
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
      ∫ x in (fun w => (arrival 0 w, marks 0 w)) ⁻¹'
          (Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)}),
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal
                ((t : ℝ) - (arrival 0 x, marks 0 x).1 / (y : ℝ)))
              ω).toNat = k}).toReal ∂Q := by
  sorry
