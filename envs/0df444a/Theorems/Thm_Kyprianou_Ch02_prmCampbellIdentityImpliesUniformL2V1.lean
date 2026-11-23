-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCampbellIdentityImpliesUniformL2V1
-- name    : Kyprianou.Ch02.prmCampbellIdentityImpliesUniformL2V1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:21:01.394064+00:00
-- url     : https://prove2.me/theorems/4257f6b8-a157-467c-8896-d02fd38c50b3
-- title:
--   L2-convergent simple marks have uniformly bounded KLS Poisson L2 norms under Campbell moments
-- statement:
--   Assume the exact Campbell second-moment formula for each simple-mark Poisson random integral. Under convergence in L2 of the restricted Lévy measure to the identity and the identity's square-integrability, show the liminf random L2 norm is finite. This is a deterministic measure-Lp and real-arithmetic consequence of the Campbell formula, deliberately separated from stochastic independence.
-- source:
--   Kyprianou (2006), Chapter 2; L2 convergence and uniform second-moment estimates

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmCampbellIdentityImpliesUniformL2V1
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
          (f n) z.2 ∂(N.N ω)) 2 P)
    (hCampbell : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        (f n) z.2 ∂(N.N ω)) ^ 2 ∂P) =
        (t : ℝ) * (∫ x in B, ((f n) x) ^ 2 ∂ν) +
          ((t : ℝ) * (∫ x in B, (f n) x ∂ν)) ^ 2) :
    ∀ t : ℝ≥0, Filter.liminf
      (fun n => eLpNorm
        (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P)
      Filter.atTop < ⊤ := by sorry
