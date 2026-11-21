-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentIncrementsOfJointProductLawV2
-- name    : Kyprianou.Ch01.independentIncrementsOfJointProductLawV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:49:24.426436+00:00
-- url     : https://prove2.me/theorems/8d084cdf-f196-41d5-af52-10983f86051d
-- title:
--   Finite-dimensional joint increment product law implies independent increments (correct sample binder)
-- statement:
--   For a probability-normalised real-valued nonnegative-time process with a.e. measurable coordinates, independence of all increments along every nondecreasing finite partition follows directly from the factorisation of each joint increment law into the product of its marginals. This is precisely the pinned Mathlib theorem ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map, with increment measurability proved from measurable process coordinates. It isolates the genuine Brownian strong-Markov obligation as a joint-product-law theorem for the first-passage clock. V1 publication failed because the lambda 'fun ω k : Fin n' assigned type Fin n to both binders. V2 uses distinct types Ω and Fin n.
-- source:
--   Lévy process independent-increments axiom and Mathlib finite product characterisation of independence.

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentIncrementsOfJointProductLawV2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ s : ℝ≥0, AEMeasurable (T s) P)
    (hJoint : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0),
      Monotone t →
      P.map (fun (ω : Ω) (k : Fin n) =>
        increment T (t k.castSucc) (t k.succ) ω) =
      Measure.pi (fun k : Fin n =>
        P.map (increment T (t k.castSucc) (t k.succ)))) :
    HasIndependentIncrements T P := by sorry
