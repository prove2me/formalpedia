-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_PathRegularity_lintegral_sq_sub_cellTimeAverage_U_le_of_lipschitz
-- name    : LevyStochCalc.BSDEJ.PathRegularity.lintegral_sq_sub_cellTimeAverage_U_le_of_lipschitz
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:38:06.232419+00:00
-- url     : https://prove2.me/theorems/205f4c5f-4292-4768-9102-8a7164e5eebb
-- title:
--   lintegral sq sub cellTimeAverage U le of lipschitz
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.PathRegularity.lintegral_sq_sub_cellTimeAverage_U_le_of_lipschitz` is extracted from `LevyStochCalc.BSDEJ.CellAverageRateMarked`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a separated Lipschitz marked integrand

For a marked integrand `U s ω e = h s * φ e` whose time factor obeys `|h s - h t| ≤ K * |s - t|`
and a strictly monotone partition `0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise
average of `U` over the cell `(t_n, t_{n+1}]` containing `s` differs from `U s ω e` by at most
`K * δ * |φ e|`, so the marked energy of `U - cellTimeAverage_U π U` over the horizon
`[0, T]` is at most `(K * δ) ^ 2 * T` times the mark integral `∫⁻ e, ‖φ e‖₊ ^ 2 ∂ν`.

The integrand treated here is deterministic in the sample point and its mark dependence is a
single separated factor. The cell-average rate for a marked integrand of general form is a
different statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u v

section Separated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ} {φ : E → ℝ}

omit [MeasurableSpace Ω] in

theorem _root_.LevyStochCalc.BSDEJ.PathRegularity.lintegral_sq_sub_cellTimeAverage_U_le_of_lipschitz (ν : Measure E)
    (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖h s * φ e
        - cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by sorry
