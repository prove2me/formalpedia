-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensityFiniteCutV1
-- name    : Kyprianou.Ch03.esscherDensityFiniteCutV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:15:28.964807+00:00
-- url     : https://prove2.me/theorems/e939e617-26cc-4e11-98c6-e87492aefbb3
-- title:
--   Esscher density restricted to finite stopping-time cuts
-- statement:
--   On each event A intersect {tau ≤ n}, upper grid approximations to tau and the deterministic-time density identity give the stopped density identity and integrability.
-- source:
--   Kyprianou (2006), Corollary 3.11; decomposition of 87ef6563-5569-47b4-b375-99ef3353c600

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem Kyprianou.Ch03.esscherDensityFiniteCutV1
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
      tau omega = (tauFinite omega : WithTop NNReal)) :
    ∀ (A : Set Omega),
      (∀ t : NNReal, MeasurableSet[F t] (A ∩ {omega : Omega | tau omega ≤ (t : WithTop NNReal)})) →
      ∀ n : ℕ, Integrable ((A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}).indicator (fun eta : Omega => esscherDensity X beta (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta)) P ∧
        Q (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}) = ENNReal.ofReal (∫ omega, (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}).indicator (fun eta : Omega => esscherDensity X beta (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta) omega ∂P) := by sorry
