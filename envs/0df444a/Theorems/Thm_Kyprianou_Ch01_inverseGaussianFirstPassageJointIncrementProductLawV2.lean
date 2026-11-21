-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageJointIncrementProductLawV2
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageJointIncrementProductLawV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T00:49:32.413014+00:00
-- url     : https://prove2.me/theorems/f7c45831-711b-4485-aa31-5113c269afcb
-- title:
--   Brownian inverse-Gaussian first-passage increment vector has product law (correct sample binder)
-- statement:
--   For the inverse-Gaussian Brownian first-passage clock, the joint law of the level-indexed passage-time increments along every finite nondecreasing barrier partition is the product of the individual increment laws. This is the genuine stochastic factorisation needed for independent increments. A sound proof uses strong Markov at successive finite first-passage stopping times and deterministic first-passage additivity after spatial shift. The pinned Mathlib iIndepFun_iff_map_fun_eq_pi_map lemma proves the original independent-increments axiom directly once this joint law and measurable coordinates are established. The n=0 and zero-length partition segments require no stochastic argument. V1 publication failed because the lambda 'fun ω k : Fin n' assigned type Fin n to both binders. V2 uses distinct types Ω and Fin n.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strong Markov at successive upper-passage times.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageJointIncrementProductLawV2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0),
      Monotone t →
      P.map (fun (ω : Ω) (k : Fin n) =>
        ProbabilityTheory.increment T (t k.castSucc) (t k.succ) ω) =
      Measure.pi (fun k : Fin n =>
        P.map (ProbabilityTheory.increment T (t k.castSucc) (t k.succ))) := by sorry
