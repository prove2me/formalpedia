-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_le_of_real_lower_bound_readable
-- name    : FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:44.608072+00:00
-- url     : https://prove2.me/theorems/36c3f5d5-3ca4-4d66-abff-68d4394870f7
-- title:
--   Legendre Upper Bound from a Bounded Domain and Real Floor
-- statement:
--   This bounds the actual extended-real Legendre transform using a bounded effective domain.
--
--   Let $\phi:E\to\overline{\mathbb R}$, let $L\in[0,\infty)$, and let $m\in\mathbb R$. Assume:
--
--   1. $\phi(y)\neq-\infty$ for every $y$;
--   2. if $\phi(y)\neq+\infty$, then $\|y\|\leq L$;
--   3. $m\leq\phi(y)$ for every $y$.
--
--   Then for every $x\in E$,
--
--   $$
--   \operatorname{Leg}(\phi)(x)
--   \leq
--   L\|x\|-m,
--   $$
--
--   with the right-hand side coerced into `EReal`. The statement controls the full extended-real supremum and does not assume finite dimensionality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_le_of_real_lower_bound
--       (φ : E → EReal) (L : NNReal) (m : ℝ)
--       (hbot : ∀ y, φ y ≠ ⊥)
--       (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
--       (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
--       legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/BoundedConjugate`](https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`exists_real_global_minimum_of_bounded_domain`](https://prove2.me/theorems/7afbf80a-1864-49d4-8e93-ff4674a5643f) · Next: [`real_convexOn_legendre`](https://prove2.me/theorems/fbb08d4f-988c-4d02-8aba-5ffd7f1a1919).
--
--   [Source excerpt, lines 107–112](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L107-L112) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L104-L136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

open MeasureTheory Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_readable
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
    legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by sorry
