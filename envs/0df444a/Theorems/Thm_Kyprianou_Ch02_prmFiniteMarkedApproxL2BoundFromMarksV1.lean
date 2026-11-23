-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkedApproxL2BoundFromMarksV1
-- name    : Kyprianou.Ch02.prmFiniteMarkedApproxL2BoundFromMarksV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:44:48.960398+00:00
-- url     : https://prove2.me/theorems/a127e321-0ea1-45d0-ba29-94e47b36e15f
-- title:
--   KLS marked-Poisson L2 approximation transferred from simple mark convergence
-- statement:
--   Given a finite-band square-integrable Lévy real mark and an explicit sequence of finite-range simple real mark functions converging to identity both pointwise and in L2 of the restricted intensity, construct finite weighted KLS Poisson count approximants to the actual signed marked integral with a.s. convergence and finite liminf of L2 norms. The remaining proof uses the already proved simple-mark pathwise convergence, fibre sum formula, finite count moments, and Poisson Campbell/isometry to bound quadratic moments.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9; KLS marked-PRM finite-simple approximation and second moments

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteMarkedApproxL2BoundFromMarksV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfpoint : ∀ x : ℝ,
      Filter.Tendsto (fun n => (f n) x) Filter.atTop (nhds x))
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0)) :
    ∀ t : ℝ≥0,
      ∃ (F : ℕ → Finset ℕ)
        (C : ℕ → ℕ → Set (ℝ × ℝ)) (a : ℕ → ℕ → ℝ),
        (∀ n i, i ∈ F n → MeasurableSet (C n i)) ∧
        (∀ n i, i ∈ F n →
          LevyStochCalc.Poisson.referenceIntensity ν (C n i) ≠ ⊤) ∧
        (∀ n i, i ∈ F n →
          C n i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∧
        (∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun n => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            Filter.atTop
            (nhds (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)))) ∧
        Filter.liminf
          (fun n => eLpNorm
            (fun ω => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            2 P) Filter.atTop < ⊤ := by sorry
