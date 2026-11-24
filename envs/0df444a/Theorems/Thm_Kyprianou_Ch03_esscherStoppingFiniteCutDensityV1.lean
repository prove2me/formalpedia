-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherStoppingFiniteCutDensityV1
-- name    : Kyprianou.Ch03.esscherStoppingFiniteCutDensityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:09:59.2908+00:00
-- url     : https://prove2.me/theorems/966cfd9c-5ef2-4a4a-b2b5-9ff175ba0f61
-- title:
--   Esscher likelihood on a finite stopping-time event
-- statement:
--   On A intersect {tau <= n}, the actual stopped Esscher likelihood is a.e. measurable and its nonnegative integral equals Q of that event. Use finite upper-grid stopping times and uniform integrability from the fixed deterministic horizon density.
-- source:
--   Kyprianou (2006), Corollary 3.11; finite-horizon restriction and monotone exhaustion

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem Kyprianou.Ch03.esscherStoppingFiniteCutDensityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P))
    (tau : Omega -> WithTop NNReal)
    (hStopping : IsStoppingTime F tau)
    (tauFinite : Omega -> NNReal)
    (hTauFinite : forall omega, tau omega != ⊤ ->
      tau omega = (tauFinite omega : WithTop NNReal))
    (A : Set Omega)
    (hA : forall t : NNReal,
      MeasurableSet[F t] (A ∩ {omega : Omega | tau omega ≤ (t : WithTop NNReal)}))
    (n : Nat) :
    let B := A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}
    let g := fun eta : Omega => esscherDensity X beta
      (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta
    AEMeasurable (Set.indicator B g) P ∧
      Q B = ∫⁻ omega, ENNReal.ofReal (Set.indicator B g omega) ∂P := by sorry
