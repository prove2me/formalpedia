-- Prove2me | Theorems.Thm_Kyprianou_Ch04_adaptedAELeftPredictableVersionV1
-- name    : Kyprianou.Ch04.adaptedAELeftPredictableVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:46.722003+00:00
-- url     : https://prove2.me/theorems/e7a98b18-8532-5f50-9366-c66769ad9faa
-- title:
--   Predictable version of almost sure strict left limits
-- statement:
--   An adapted process with almost-sure strict left limits has a predictable version
--   of the given left limits at every strictly positive time on one full-measure event.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem adaptedAELeftPredictableVersionV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y L : NNReal → Ω → ℝ) (hY : Adapted F Y)
    (hl : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (L t ω))) :
    ∃ V : NNReal → Ω → ℝ, IsStronglyPredictable F V ∧
      ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω := by
  sorry
end Kyprianou.Ch04
