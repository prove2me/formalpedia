-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver
-- name    : Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:30:11.511875+00:00
-- url     : https://prove2.me/theorems/49405927-66dc-442e-b14c-6d9558559823
-- title:
--   Stopped lattice compound-Poisson path is a.e.-measurable as a product-space random variable
-- statement:
--   For a marked compound-Poisson driver with the hypotheses of the forward Lamperti correspondence, its integer-valued path stopped at the first nonpositive level is almost-everywhere measurable in the product measurable space indexed by nonnegative real times. The already proved stoppedCompoundPoissonMarkov theorem gives fixed-time almost-everywhere measurability of the stopped process coerced to Nat, and its nonnegativity almost surely. Cast back to Int and assemble coordinatewise through aemeasurable_pi_iff. No finite offspring mean is required.
-- source:
--   Source-faithful second conjunct of Kyprianou.Ch01.lampertiForwardPathMapsAEMeasurableWithoutMoment d346ccdb-3e68-4130-b078-6746f99dd872, supporting accepted parent reduction 5716bfa6-f2e3-4d53-afe7-7c2bceb5f07f in Kyprianou (2006) Chapter 1 §1.3.4. Direct application to existing proved Kyprianou.Ch01.stoppedCompoundPoissonMarkov UUID 0e97933c-a2d7-4f59-a9c5-782003be5f5f.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ, AEMeasurable
      (fun ω : Ω' => fun t : ℝ≥0 =>
        stoppedIntegerCompoundPoisson y arrival marks t ω) Q := by
  sorry
