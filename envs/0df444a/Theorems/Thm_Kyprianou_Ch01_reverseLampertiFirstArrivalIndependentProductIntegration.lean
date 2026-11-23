-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalIndependentProductIntegration
-- name    : Kyprianou.Ch01.reverseLampertiFirstArrivalIndependentProductIntegration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:29:41.792199+00:00
-- url     : https://prove2.me/theorems/781bb03f-3f83-4080-ad11-91cc5c26c3e2
-- title:
--   First-marked-arrival renewal probability by Fubini under explicit product-driver law
-- statement:
--   Evaluate the post-first-event reverse-Lamperti population probability as the offspring-weighted exponential integral, assuming the explicitly provided independent first holding-time/mark pair law, independent infinite shifted tail, unchanged shifted compound-Poisson driver, and full independent sequence law. Remaining work is measurable pushforward, tail-law transfer to K, Fubini, and first-arrival exponential integration.
-- source:
--   Kyprianou (2006), Section 1.3.4; analytic conditional first-jump renewal after separating genuine stochastic independence prerequisites.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstArrivalIndependentProductIntegration
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hHeadLaw : HasLaw
      (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (hFullProductLaw : HasLaw
      (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    (Q (⋃ j : ℕ, {ω |
          marks 0 ω = (j : ℝ) - 1 ∧
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) + j)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω)})).toReal =
        ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
          (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j)
                (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  sorry
