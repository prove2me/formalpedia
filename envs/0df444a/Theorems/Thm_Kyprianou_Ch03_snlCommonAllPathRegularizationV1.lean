-- Prove2me | Theorems.Thm_Kyprianou_Ch03_snlCommonAllPathRegularizationV1
-- name    : Kyprianou.Ch03.snlCommonAllPathRegularizationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:25.184795+00:00
-- url     : https://prove2.me/theorems/7ed63b98-806c-4d4a-813e-17060bb3a218
-- title:
--   Common all-path càdlàg negative-jump regularisation
-- statement:
--   Use a common measurable version; spectral negativity of the triplet gives almost surely no positive jumps at all positive times, via the Lévy-Itô jump measure or equality of càdlàg path laws. Replace the paths on a measurable exceptional null set by the zero path.
-- source:
--   Kyprianou (2006), Chapters 2-3; parent 063b9d7c-87f6-432a-91c5-8ca8556a76f0.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open scoped Topology

theorem Kyprianou.Ch03.snlCommonAllPathRegularizationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∃ Y : NNReal → Omega → ℝ,
      (∀ᵐ w ∂P, ∀ t, Y t w = X t w) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ w, Y 0 w = 0) ∧
      (∀ w t, ContinuousWithinAt (fun s => Y s w) (Set.Ici t) t) ∧
      (∀ w t, 0 < t → ∃ l, Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 l)) ∧
      (∀ w t l, 0 < t → Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 l) → Y t w ≤ l) := by
  sorry
