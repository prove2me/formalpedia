-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_source017
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:38:07.673043+00:00
-- url     : https://prove2.me/theorems/15c55202-44da-420f-bf88-f910c0e7060c
-- title:
--   Arithmetic lower bound for a nonzero selected interpolation minor
-- statement:
--   For fixed approximation data $d$, a positive interpolation scale $H$, and a selection of columns whose interpolation minor has nonzero determinant, let $b(H)$ be the actual mean row weight and $M(H)$ the actual row count. The source arithmetic estimate gives
--
--   $$-\bigl(1-b(H)\bigr)-e_{\mathrm{ar}}(d)\le \frac{\log|\det A_{\mathrm{minor}}(H)|}{M(H)H}.$$
--
--   Here $e_{\mathrm{ar}}(d)$ is the arithmetic error stored in the campaign's original fixed data. This is the exact original source interface, currently published as an Open dependency for the NoFixedData reduction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L74-L85

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017 {nu : ℝ} (d : FixedData nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  sorry
