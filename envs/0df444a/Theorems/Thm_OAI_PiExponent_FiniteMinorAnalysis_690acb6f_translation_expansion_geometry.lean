-- Prove2me | Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_translation_expansion_geometry
-- name    : OAI.PiExponent.FiniteMinorAnalysis_690acb6f.translation_expansion_geometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:27:26.269302+00:00
-- url     : https://prove2.me/theorems/17659df9-f325-4ff2-b02f-19bb255e9416
-- title:
--   Finite literal translation expansion and index geometry
-- statement:
--   The exact finite rational-center minor is a finite sum of translated period minors. The same finite index geometry gives a positive row count, a polynomial per-row choice bound, the mean-weight identity, and the low-weight capacity bound. The assumptions allow A = 0; the zero transverse index keeps the low-weight set nonempty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.FiniteMinorAnalysis_690acb6f.translation_expansion_geometry
    {m : ℕ} (K : ℕ) (w0 v theta F A H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hA : 0 ≤ A) (hH : 0 < H) (hq : ∀ i, 2 ≤ q i) :
    0 < rowCount K v theta q H ∧
    Fintype.card (Choices K v theta q H) ≤
      termCount m v H ^ rowCount K v theta q H ∧
    (∑ r : Rows K v theta q H, weight q (beta r)) =
      (rowCount K v theta q H : ℝ) * H *
        MatrixArithmetic.meanRowWeight K v theta q H ∧
    (∀ a : Transverse q H, 0 ≤ weight q a.1) ∧
    0 < lowCount q A H ∧
    (((Finset.univ : Finset (Transverse q H)).filter
      (fun a => weight q a.1 ≤ A * H)).card : ℝ) ≤ (lowCount q A H : ℝ) ∧
    (∀ selection : Rows K v theta q H → Columns w0 q H,
      (MatrixArithmetic.selectedMinor K w0 v theta F H p q selection).det =
        ∑ f : Choices K v theta q H,
          (∏ r, scalar F p q r (f r)) * (periodMatrix selection f).det) := by sorry
