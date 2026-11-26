-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositiveSubordinatorMarginalsV2
-- name    : Kyprianou.Ch05.canonicalPositiveSubordinatorMarginalsV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:53:35.390541+00:00
-- url     : https://prove2.me/theorems/564a2e4b-4235-4db1-a05b-4f8921813955
-- title:
--   Uncompensated positive Poisson path is a Levy process with the prescribed killed-subordinator marginals
-- statement:
--   Construct the finite-variation positive Poisson integral with drift. Use the public Chapter 2 Poisson integral laws, independent disjoint region sigma algebras, and the real Laplace anchor to identify marginals. Establish independent stationary increments and ae cadlag regularity without importing the conflicting characteristic exponent module.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.canonicalPositiveSubordinatorMarginalsV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    IsLevyProcess X Q ∧ ∀ t : NNReal, P.map (Y t) = Q.map (X t) := by
  sorry
