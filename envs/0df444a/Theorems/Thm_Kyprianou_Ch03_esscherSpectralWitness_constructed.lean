-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherSpectralWitness_constructed
-- name    : Kyprianou.Ch03.esscherSpectralWitness_constructed
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:07:53.415024+00:00
-- url     : https://prove2.me/theorems/9f58ebc2-2f3d-434c-8014-a796ac63ecb3
-- title:
--   Corollary 3.10 witness component 0
-- statement:
--   A sound sufficient bridge for the original source, sharing the single Esscher-transformed witness. The conditional premises are supplied by the separate witness-construction theorem.
-- source:
--   Kyprianou (2006), Chapter 3, Corollary 3.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem esscherSpectralWitness_constructed
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
      Lbeta.X = L.X ∧ Lbeta.σ = L.σ ∧ Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧ Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν) := by
  sorry

end Kyprianou.Ch03
