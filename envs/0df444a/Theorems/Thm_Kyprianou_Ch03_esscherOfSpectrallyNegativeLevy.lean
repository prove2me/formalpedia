-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherOfSpectrallyNegativeLevy
-- name    : Kyprianou.Ch03.esscherOfSpectrallyNegativeLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:41:18.514396+00:00
-- url     : https://prove2.me/theorems/6621799c-a836-4388-bebf-94157483b2b9
-- title:
--   Corollary 3.10: spectrally negative Esscher transforms and shifted Laplace exponent
-- statement:
--   For a spectrally negative Levy process L and any beta>=0, the Esscher-transformed measure Q with F_t density exp(beta*X_t-t*psi(beta)) yields a spectrally negative Levy process with exactly the original sample process. The Gaussian coefficient is unchanged, the negative Levy measure is tilted by exp(beta*x), the drift has the corresponding positive-exponent change, and the Laplace exponent is psi(theta+beta)-psi(beta) for all theta>=-beta, including the edge theta=-beta. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, Corollary 3.10, printed p. 80; text surrounding the corollary has reversed jump-support sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem esscherOfSpectrallyNegativeLevy
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNatural : IsCompletedNaturalFiltration P L.X F)
    (beta : Real) (hBeta : 0 <= beta)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)) :
    exists (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      Lbeta.X = L.X ∧
      Lbeta.σ = L.σ ∧
      Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν) ∧
      forall theta : Real, -beta <= theta ->
        Lbeta.ψ theta = L.ψ (theta + beta) - L.ψ beta := by
  sorry
end Kyprianou.Ch03
