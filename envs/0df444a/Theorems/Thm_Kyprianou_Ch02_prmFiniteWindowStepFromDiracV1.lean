-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowStepFromDiracV1
-- name    : Kyprianou.Ch02.prmFiniteWindowStepFromDiracV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:00:38.222088+00:00
-- url     : https://prove2.me/theorems/d58c60f4-1690-4403-b20f-0244613a3283
-- title:
--   Finite-window Dirac representation implies uniform cumulative marked-step integral representation
-- statement:
--   At each integer horizon, apply the finite Dirac measure identity to the integrand p↦1_{p.time≤t}p.mark. For every t≤T the integral over (0,t]×B equals the same finite weighted sum of right-continuous step indicators. Requires integration of a finite sum of weighted Dirac measures, with finite masses ensured by the Poisson count law, as in upstream LevyStochCalc/Poisson/JumpSum.lean.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.8, actual arbitrary LevyStochCalc PoissonRandomMeasure finite-window decomposition, connected to Eq (2.3) via Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV1 (d17f62e1-b633-4f68-826e-8975dd391109).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteWindowStepFromDiracV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hDirac : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0 := by sorry
