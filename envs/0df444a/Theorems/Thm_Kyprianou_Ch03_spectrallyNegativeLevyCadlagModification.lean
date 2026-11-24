-- Prove2me | Theorems.Thm_Kyprianou_Ch03_spectrallyNegativeLevyCadlagModification
-- name    : Kyprianou.Ch03.spectrallyNegativeLevyCadlagModification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:47:59.150269+00:00
-- url     : https://prove2.me/theorems/063b9d7c-87f6-432a-91c5-8ca8556a76f0
-- title:
--   General Lévy to spectrally negative all-path càdlàg representative
-- statement:
--   Bridge from an almost-surely càdlàg Lévy process to an everywhere-càdlàg representative with the same complete paths almost surely and the original spectrally negative triplet. Does not impose a stronger all-path hypothesis on the generic source.
-- source:
--   Kyprianou (2006), Chapters 2-3; Lévy–Itô decomposition and spectrally negative class.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem spectrallyNegativeLevyCadlagModification
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∃ (Y : NNReal → Omega → ℝ)
      (L : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega) ∧
      L.X = Y ∧ L.ν = T.levyMeasure ∧
      L.σ ^ 2 = (T.gaussianVariance : ℝ) := by
  sorry

end Kyprianou.Ch03
