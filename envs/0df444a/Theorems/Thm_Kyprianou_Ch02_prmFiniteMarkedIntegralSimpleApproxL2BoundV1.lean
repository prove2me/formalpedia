-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkedIntegralSimpleApproxL2BoundV1
-- name    : Kyprianou.Ch02.prmFiniteMarkedIntegralSimpleApproxL2BoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:09:01.87009+00:00
-- url     : https://prove2.me/theorems/90e953d7-7c00-4e80-9336-d654433561a8
-- title:
--   Finite-simple marked Poisson approximation with uniformly bounded quadratic moments
-- statement:
--   The raw integral of real marks over a finite-intensity Poisson time strip is the almost-sure pointwise limit of finite weighted sums of finite-intensity Poisson counts, whose second L2 norm liminf is finite. Each simple cell is measurable, of finite Poisson reference intensity and confined to the strip. The finite-dimensional weighted count L2 theorem and the pinned Lp Fatou inequality then establish the target quadratic-moment integrability. The substantive missing proof is the Poisson marked Campbell second-moment bound that makes the approximations uniformly square-integrable.
-- source:
--   Kyprianou Chapter 2 Lemma 2.9 quadratic mark-moment estimate and KLS PRM; source-faithful approximation to canonical 01907697-a538-4205-9a2f-75e9fc04a42d

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteMarkedIntegralSimpleApproxL2BoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
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
