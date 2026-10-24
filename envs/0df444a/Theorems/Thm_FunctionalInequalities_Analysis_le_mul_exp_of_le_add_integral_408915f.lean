-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_le_mul_exp_of_le_add_integral_408915f
-- name    : FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:05.761914+00:00
-- url     : https://prove2.me/theorems/0a4ac77c-4cf4-406f-9f73-677cadb97028
-- title:
--   Integral Grönwall Bound
-- statement:
--   This statement is an integral Grönwall inequality.
--
--   Let φ:ℝ→ℝ and a,K,T∈ℝ. Assume K≥0, φ is measurable, φ is bounded on $[0,T]$, and for every t∈[0,T],
--
--   $$φ(t)\leq a+K\int_{(0,t]}φ(s)\,ds.$$
--
--   Then for every t∈[0,T],
--
--   $$φ(t)\leq a e^{Kt}.$$
--
--   This provides a real-analysis form of Grönwall's inequality for a measurable bounded function and an arbitrary real initial coefficient a.
--
--   **Formalization Note** The integral is over `Set.Ioc 0 t`; the theorem does not assume T≥0 separately, although the interval hypotheses govern its scope.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Gronwall.lean#L18-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Gronwall`, declaration `FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral`; the repository is private at upload time).

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral_408915f {φ : ℝ → ℝ} {a K T : ℝ} (hK : 0 ≤ K)
    (hφm : Measurable φ) (hφb : ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, |φ t| ≤ B)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a + K * ∫ s in Set.Ioc (0 : ℝ) t, φ s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a * Real.exp (K * t) := by sorry
