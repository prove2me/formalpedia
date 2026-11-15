-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensityAtExtendedStoppingTime
-- name    : Kyprianou.Ch03.esscherDensityAtExtendedStoppingTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:41:50.143185+00:00
-- url     : https://prove2.me/theorems/87ef6563-5569-47b4-b375-99ef3353c600
-- title:
--   Corollary 3.11: Esscher Radon-Nikodym density at an extended stopping time
-- statement:
--   Under the full Theorem 3.9 large-jump exponential moment hypotheses and Esscher finite-horizon Radon-Nikodym density, for any extended F-stopping time tau and any event A in F_tau, the Esscher probability of A together with {tau finite} equals the original expectation of exp(beta X_tau-tau psi(beta)) on exactly that event. The formula remains restricted to {tau finite}, and tau is not artificially bounded. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, Corollary 3.11, printed p. 80.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem esscherDensityAtExtendedStoppingTime
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
    forall (A : Set Omega),
      (forall t : NNReal,
        MeasurableSet[F t]
          (Set.inter A {omega : Omega |
            tau omega <= (t : WithTop NNReal)})) ->
      Q (Set.inter A {omega : Omega | tau omega != ⊤}) =
        ENNReal.ofReal
          (∫ omega,
            Set.indicator
              (Set.inter A {eta : Omega | tau eta != ⊤})
              (fun eta : Omega =>
                esscherDensity X beta
                  (Real.log
                    (∫ z, Real.exp (beta * X 1 z) ∂P))
                  (tauFinite eta) eta)
              omega ∂P) := by
  sorry
end Kyprianou.Ch03
