-- Prove2me | Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_finiteGridBadIncrement_le
-- name    : MarkovProcess.IsKolmogorovProcess.measure_finiteGridBadIncrement_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:03:43.598973+00:00
-- url     : https://prove2.me/theorems/e23280cb-2fc0-4944-b4f7-f00c97c2124b
-- title:
--   Finite-grid Kolmogorov increment event probability bound
-- statement:
--   A finite-grid union bound controls the measure of at least one large adjacent increment by the Kolmogorov moment condition and the maximum grid spacing. This theorem is the original result of Scott Armstrong, MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteGridIncrement.lean#L32-L64

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.IsKolmogorovProcess.measure_finiteGridBadIncrement_le
    {T : Type*} [PseudoEMetricSpace T] {N : ℕ} {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M)
    (grid : Fin (N + 1) → T) (δ ε : ℝ≥0∞)
    (hgrid : ∀ i : Fin N, edist (grid i.castSucc) (grid i.succ) ≤ δ)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X grid p ε) ≤ N * (M * δ ^ q / ε ^ p) := by sorry
