-- Prove2me | Theorems.Thm_Kyprianou_exercise2_6_AllPartsCh02V3
-- name    : Kyprianou.exercise2_6_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:24:14.825267+00:00
-- url     : https://prove2.me/theorems/2d7732b0-159a-41c5-9727-2eb4777ea9df
-- title:
--   Exercise 2.6: corrected jump-power expectation and compensated martingale
-- statement:
--   Part (i) corrects the false printed almost-sure finiteness criterion to the mathematically valid finite-expectation equivalence for the nonnegative absolute jump-power integral; part (ii) asserts the compensated power-jump martingale when its finite large-jump moment exists. Heavy-tail counterexample documented in the source errata.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.6, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_6_AllPartsCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (t : ℝ≥0), 0 < t →
       ((∫⁻ ω, ∫⁻ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
            ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P) < ⊤ ↔
        Integrable (fun x : ℝ => |x| ^ n)
          (ν.restrict {x : ℝ | 1 ≤ |x|}))) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
        Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
        MeasureTheory.Martingale
          (fun (t : ℝ≥0) ω =>
            (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
               z.2 ^ n ∂(N.N ω)) -
            (t : ℝ) * ∫ x, x ^ n ∂ν) ℱ P)
      := by sorry

end Kyprianou
