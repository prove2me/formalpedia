-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherChangeOfMeasurePreservesLevyAndTriplet
-- name    : Kyprianou.Ch03.esscherChangeOfMeasurePreservesLevyAndTriplet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:40:41.645956+00:00
-- url     : https://prove2.me/theorems/f153b64d-c555-49f6-9313-bb720412692a
-- title:
--   Theorem 3.9: Esscher change of measure and transformed Levy triplet
-- statement:
--   Given a real Levy process with a full Levy-Khintchine triplet, beta with finite large-jump exponential moment, and a probability measure Q whose density relative to the original measure on each filtration F_t is exp(beta*X_t-t*log E[e^(beta X_1)]), the process remains Levy under Q. Its Gaussian variance is unchanged, its Levy measure is multiplied by exp(beta*x), and the drift changes by plus beta times variance plus the compensated small-jump tilt in Chapter 1's positive characteristic-exponent convention (opposite to the textbook a convention). The characteristic function has the new triplet and on the finite moment domain the Laplace exponent shifts by beta. Q is the Esscher measure characterised by its finite-horizon Radon-Nikodym property; its existence as a global extension is not asserted for arbitrary completed terminal sigma-algebras. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9, equations (3.10)-(3.13), pp. 78-80.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherChangeOfMeasurePreservesLevyAndTriplet
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
                t omega) omega ∂P)) :
    exists (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧
      Tbeta.gaussianVariance = T.gaussianVariance ∧
      Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      ProbabilityTheory.IsLevyProcess X Q ∧
      (forall (t : NNReal) (xi : Real),
        charFun (Q.map (X t)) xi =
          Complex.exp ((((t : Real) : Complex)) *
            Kyprianou.Ch01.levyTripleExponent Tbeta xi)) ∧
      (forall theta : Real,
        Integrable (fun omega => Real.exp ((theta + beta) * X 1 omega)) P ->
        Real.log (∫ omega, Real.exp (theta * X 1 omega) ∂Q) =
          Real.log
            (∫ omega, Real.exp ((theta + beta) * X 1 omega) ∂P) -
          Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)) := by
  sorry

end Kyprianou.Ch03
