-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_bound_of_log_lower_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:03.286987+00:00
-- url     : https://prove2.me/theorems/98239541-fa41-45b3-93db-26285bcefb48
-- title:
--   Boundedness From A Logarithmic Lower Bound
-- statement:
--   This is an elementary coercivity lemma for real parameters.
--
--   For $A,b\in\mathbb R$ and $n\in\mathbb N$, there exists $B\ge0$ such that every $M\ge0$ satisfying
--   $$b\le\log A+n\log\max\{M,1\}-M$$
--   also satisfies
--   $$M\le B.$$
--
--   The conclusion converts a lower bound on the logarithmic coercivity expression into a uniform upper bound on $M$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_bound_of_log_lower (A : ℝ) (n : ℕ) (b : ℝ) :
--       ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 0 ≤ M →
--         b ≤ Real.log A + (n : ℝ) * Real.log (max M 1) - M → M ≤ B
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Coercivity`](https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c).
--
--   Previous: [`exists_coercivity_of_centered_probability`](https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2) · Next: [`exists_integral_bound_of_eventual_functional_lower`](https://prove2.me/theorems/ec1ab899-a2cd-4af7-a22e-cf39c5c47111).
--
--   [Source excerpt, lines 213–215](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L213-L215) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L211-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

theorem FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower_readable (A : ℝ) (n : ℕ) (b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 0 ≤ M →
      b ≤ Real.log A + (n : ℝ) * Real.log (max M 1) - M → M ≤ B := by sorry
