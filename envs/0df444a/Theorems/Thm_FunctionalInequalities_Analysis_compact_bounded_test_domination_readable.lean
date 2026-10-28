-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_compact_bounded_test_domination_readable
-- name    : FunctionalInequalities.Analysis.compact_bounded_test_domination_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:42.341495+00:00
-- url     : https://prove2.me/theorems/598f7c40-05a7-49e8-94fe-b29d9620425b
-- title:
--   Compact Support Domination for Bounded Tests
-- statement:
--   This gives an integrable domination statement for a compactly supported bounded test.
--
--   Let $F,\eta:\mathbb R^n\to\mathbb R$, let $S\subseteq\mathbb R^n$ be compact, and let $C\in\mathbb R$. Assume $F$ is locally integrable, $\eta$ is almost-everywhere strongly measurable, $\operatorname{supp}(\eta)\subseteq S$, and $\|\eta(x)\|\le C$ for every $x$. Then
--
--   $$
--   \mathbf 1_S(x)C\|F(x)\|
--   $$
--
--   is integrable, and for every $x$,
--
--   $$
--   \|F(x)\eta(x)\|\le \mathbf 1_S(x)C\|F(x)\|.
--   $$
--
--   Consequently $x\mapsto F(x)\eta(x)$ is integrable with respect to volume measure. The Lean declaration is `compact_bounded_test_domination_readable`; the hypotheses are pointwise except for the stated a.e. measurability condition.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compact_bounded_test_domination {n : ℕ}
--       {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
--       {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hS : IsCompact S)
--       (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
--       Integrable (S.indicator fun x => C * ‖F x‖)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
--         Integrable (fun x => F x * η x)
--           (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Previous: [`integral_weakDeriv_mul_eq_swap`](https://prove2.me/theorems/61cf322f-0c0f-4f7d-8765-ac88a842a6c5) · Next: [`integral_flux_eq_neg_forcing_of_bounded_weak_test`](https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8).
--
--   [Source excerpt, lines 1089–1099](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1089-L1099) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1088-L1117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.compact_bounded_test_domination`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set

theorem FunctionalInequalities.Analysis.compact_bounded_test_domination_readable {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
