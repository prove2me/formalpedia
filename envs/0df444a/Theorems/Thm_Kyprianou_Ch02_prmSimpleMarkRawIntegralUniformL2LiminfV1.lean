-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawIntegralUniformL2LiminfV1
-- name    : Kyprianou.Ch02.prmSimpleMarkRawIntegralUniformL2LiminfV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:10:20.750845+00:00
-- url     : https://prove2.me/theorems/c7b0dbf9-2022-4cbf-bdd2-d97a86afabc6
-- title:
--   Uniform L2 moment estimate for KLS marked Poisson simple approximations
-- statement:
--   If deterministic finite-range real marks converge in L2 to the identity mark under the finite restricted Lévy intensity, and their original KLS finite-window random integrals are square-integrable, the liminf of their random L2 norms remains finite. This is the uniform Poisson/Campbell second-moment estimate required for Theorem 2.10's finite-activity precursor.
-- source:
--   Kyprianou (2006), Chapter 2, Poisson marked-integral second moments and L2 approximation

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkRawIntegralUniformL2LiminfV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0))
    (hrawL2 : ∀ t : ℝ≥0, ∀ n,
      MemLp (fun ω =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P) :
    ∀ t : ℝ≥0, Filter.liminf
      (fun n => eLpNorm
        (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P)
      Filter.atTop < ⊤ := by sorry
