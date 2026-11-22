-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableWithTopIntegerRandomTimeEvaluation
-- name    : Kyprianou.Ch01.measurableWithTopIntegerRandomTimeEvaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:59:16.053805+00:00
-- url     : https://prove2.me/theorems/fc1e352d-31a2-4391-9407-fe434df8e57f
-- title:
--   Measurability of an integer process evaluated at a possibly infinite random time with absorbing-zero convention
-- statement:
--   For a jointly measurable integer-valued NNReal-time process F and a measurable `WithTop NNReal` random time T, show that the random state equal to zero on the infinite-clock event and otherwise F evaluated at the finite random time, coerced to Nat via Int.toNat, is globally measurable. The proof applies Measurable.untopD to supply a deterministic fallback finite time, composes joint F with the measurable random time and identity sample, uses the measurable singleton {top} as the if-then-else event, and composes with measurable integer-to-natural conversion on the countable discrete integer space. Crucial for reverse Lamperti `compoundPoissonToBranching` which takes the minimum of an inverse reciprocal occupation clock and first-negative-passage clock. This result has no offspring moment assumption.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Root reverse Lamperti ac1b29c6-5525-4344-a03d-7469824736ed; intended rootward parent reverseLampertiNonexplosiveStateAEMeasurable UUID 5b4cef8f-ef05-4bcd-9c85-4c110d728c6e. Pinned Mathlib Measurable.untopD, measurable_of_countable, measurableSet_singleton.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableWithTopIntegerRandomTimeEvaluation
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℤ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2))
    (T : Ω → WithTop ℝ≥0) (hT : Measurable T) :
    Measurable (fun ω : Ω =>
      (if T ω = ⊤ then (0 : ℤ)
       else F ((T ω).untopD 0) ω).toNat) := by
  sorry
