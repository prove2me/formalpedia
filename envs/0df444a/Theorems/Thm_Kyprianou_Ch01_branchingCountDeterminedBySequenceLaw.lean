-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCountDeterminedBySequenceLaw
-- name    : Kyprianou.Ch01.branchingCountDeterminedBySequenceLaw
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:12:01.959448+00:00
-- url     : https://prove2.me/theorems/9ba03c32-87f6-435c-b5fe-796f60ff2d1e
-- title:
--   Branching count depends only on the sequence law
-- statement:
--   Let two compound Poisson sequence pairs on the same probability space have the same law $\nu$ on $(\mathbb{R}^{\mathbb{N}})\times(\mathbb{R}^{\mathbb{N}})$: the original interarrivals and marks, and the shifted pair with the zeroth coordinate removed. Fix a height $z$, a time $s$, and a population size $m$.
--
--   The branching count built from a sequence pair is the integer population obtained by running the reverse Lamperti map of the integer compound Poisson path of those sequences. If the two pairs have the same law, they produce the same population probabilities:
--   $$\mathbb{Q}(Y^z_s=m)=\mathbb{Q}(\widetilde Y^z_s=m).$$
--   Here $Y$ is built from the shifted sequences and $\widetilde Y$ from the original sequences. The shifted pair is a compound Poisson driver, and every occupation clock of the original driver exceeds every finite time.
-- source:
--   Kyprianou (2006), Section 1.3.4; the branching population is a function of the interarrival and mark sequences.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingCountDeterminedBySequenceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (ν : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    (hOrig : HasLaw (fun w => (fun n => arrival n w, fun n => marks n w)) ν Q)
    (hShift : HasLaw
      (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) ν Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)) s ω).toNat = m} =
      Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z arrival marks) s ω).toNat = m} := by
  sorry
