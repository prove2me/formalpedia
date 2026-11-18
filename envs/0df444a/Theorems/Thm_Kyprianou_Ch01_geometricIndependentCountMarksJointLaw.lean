-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricIndependentCountMarksJointLaw
-- name    : Kyprianou.Ch01.geometricIndependentCountMarksJointLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:29:05.622944+00:00
-- url     : https://prove2.me/theorems/5139bc29-7bc8-40e6-983e-3e3e0c88f13f
-- title:
--   Joint distribution of an independent stopping count and full measurable increment sequence
-- statement:
--   If a measurable count N is independent of the entire measurable real increment sequence, their joint pushforward probability measure equals the product of their marginal pushforwards. This source-exact independence identity is used when conditioning a geometrically stopped IID random sum on N in Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), independent geometric stopping count and IID sequence.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricIndependentCountMarksJointLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    P.map (fun ω => (N ω, fun n : ℕ => increment n ω)) =
      (P.map N).prod
        (P.map (fun ω => fun n : ℕ => increment n ω)) := by
  sorry
