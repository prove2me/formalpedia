-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_4StablePassageAllParts
-- name    : Kyprianou.Ch07.exercise7_4StablePassageAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T15:03:05.177178+00:00
-- url     : https://prove2.me/theorems/65e5de7f-38b3-4164-91b1-62910b2e723b
-- title:
--   Exercise 7.4: stable creeping, ladder potential, triple law and constant
-- statement:
--   Exercise 7.4 in all four parts for a stable Lévy process X of index α∈(0,2), with positive jumps and neither X nor −X a subordinator; ρ=P(X_t≥0)∈(0,1). (i) Show upward creeping is impossible, and downward creeping is also impossible when negative jumps exist. (ii) Show the actual ascending ladder potential has density proportional to h^(αρ−1)/Γ(αρ) on h>0, preserving an arbitrary positive local-time normalisation constant. (iii) On all measurable rectangles in strictly positive crossing overshoot u, barrier undershoot v≥y and distance y to the pre-crossing maximum, prove the full triple-law density c(x−y)^(αρ−1)(v−y)^(α(1−ρ)−1)/(v+u)^(1+α). (iv) Identify the unique probability normalisation c=(sin(παρ)/π)Γ(α+1)/[Γ(αρ)Γ(α(1−ρ))]. The path left limit and running maximum are genuine pre-passage quantities.
-- source:
--   Kyprianou (2006), Exercise 7.4(i)–(iv), printed pp.207–208, original PDF pp.216–217, Windows Ky.pdf sheets 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch07_QuintuplePrePassageObservables
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.4(i)-(iv): stable processes do not creep, their
ascending ladder potential has the stable density, and the
positive triple first-passage law has its exact normalising constant. -/
theorem exercise7_4StablePassageAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup : NNReal → Omega → NNReal)
    (Pi U : Measure Real)
    (b : Real) (sigma2 : NNReal)
    (alpha rho : Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hLeft : Kyprianou.Ch05.IsLeftLimitVersion P X Xleft)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hRho : 0 < rho ∧ rho < 1)
    (hNoSubordinator : (¬ ∀ᵐ omega ∂P,
          Monotone (fun t : NNReal => X t omega)) ∧
      (¬ ∀ᵐ omega ∂P,
          Monotone (fun t : NNReal => -X t omega)))
    (hPositiveJumps : 0 < Pi (Set.Ioi 0))
    (hStableScaling : ∀ t : NNReal, 0 < t →
       ∀ B : Set Real, MeasurableSet B →
         P {omega | X t omega ∈ B} =
           P {omega | ((t : Real) ^ (1 / alpha)) * X 1 omega ∈ B})
    (hPositivity : ∀ t : NNReal, 0 < t →
       P {omega | 0 ≤ X t omega} = ENNReal.ofReal rho)
    (hLocalUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X Lup)
    (hAscendingPotential : ∀ B : Set Real, MeasurableSet B →
       U B = ∫⁻ s : Real in Set.Ici 0,
         P {omega | let tau :=
           Kyprianou.Ch06.inverseLocalTime Lup (Real.toNNReal s) omega
           tau ≠ ⊤ ∧
           Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega ∈ B}
         ∂volume) :
    ((∀ x : Real, 0 < x →
        Kyprianou.Ch05.creepingProbability
           P X (fun _ => (⊤ : WithTop NNReal)) x = 0) ∧
     (Pi (Set.Iio 0) ≠ 0 →
       ∀ x : Real, 0 < x →
         Kyprianou.Ch05.creepingProbability
           P (fun t omega => -X t omega)
           (fun _ => (⊤ : WithTop NNReal)) x = 0) ∧
     (∃ cPotential : Real, 0 < cPotential ∧
       ∀ B : Set Real, MeasurableSet B →
         U B = ∫⁻ h : Real in (B ∩ Set.Ioi 0),
           ENNReal.ofReal
             (cPotential * (h ^ (alpha * rho - 1)) /
               Real.Gamma (alpha * rho)) ∂volume) ∧
     (∃ c : Real,
       0 < c ∧
       c = (Real.sin (Real.pi * alpha * rho) / Real.pi) *
         (Real.Gamma (alpha + 1) /
           (Real.Gamma (alpha * rho) *
            Real.Gamma (alpha * (1 - rho)))) ∧
       ∀ x : Real, 0 < x →
       ∀ (Au Av Ay : Set Real),
         MeasurableSet Au → MeasurableSet Av → MeasurableSet Ay →
       P {omega | let lifetime : Omega → WithTop NNReal := fun _ => ⊤
         let tau := Kyprianou.Ch05.passageFiniteTime X lifetime x omega
         Kyprianou.Ch05.PassageFinite X lifetime x omega ∧
         (X tau omega - x) ∈ Au ∧
         (x - Xleft tau omega) ∈ Av ∧
         (x - maximumBeforeUpcrossing X x omega) ∈ Ay} =
       ENNReal.ofReal c *
         ∫⁻ y : Real in (Ay ∩ Set.Icc 0 x),
           (∫⁻ v : Real in (Av ∩ Set.Ici y),
             (∫⁻ u : Real in (Au ∩ Set.Ioi 0),
               ENNReal.ofReal
                 ((x - y) ^ (alpha * rho - 1) *
                  (v - y) ^ (alpha * (1 - rho) - 1) /
                  ((v + u) ^ (1 + alpha))) ∂volume)
            ∂volume) ∂volume)) := by
  sorry

end Kyprianou.Ch07
