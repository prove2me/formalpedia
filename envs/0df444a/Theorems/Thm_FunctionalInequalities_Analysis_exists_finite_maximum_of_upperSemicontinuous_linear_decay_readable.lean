-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
-- name    : FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:04.502855+00:00
-- url     : https://prove2.me/theorems/3017df1c-42c0-4624-946f-b456d3bec309
-- title:
--   Finite Maximum Under Upper Semicontinuity and Linear Decay
-- statement:
--   This is a general finite-dimensional attainment lemma for extended-real functions.
--
--   Let $E$ be a finite-dimensional real inner-product normed space and $G:E\to\overline{\mathbb R}$. Assume:
--
--   1. $G$ is upper semicontinuous;
--   2. $G(x)\ne+\infty$ for every $x$;
--   3. $G$ is not identically $-\infty$;
--   4. there are $a,b\in\mathbb R$ with $a>0$ and
--   $$G(x)\le b-a\|x\|$$
--   for every $x\in E$.
--
--   Then there is $x\in E$ such that $G(x)$ is neither $-\infty$ nor $+\infty$, and
--   $$G(z)\le G(x)\qquad\text{for every }z\in E.$$
--
--   Values equal to $-\infty$ are allowed away from the maximizing point. The lemma is a reusable attainment principle for extended-real objectives with positive linear decay.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_finite_maximum_of_upperSemicontinuous_linear_decay
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E]
--       (G : E → EReal) (husc : UpperSemicontinuous G)
--       (hnotTop : ∀ x : E, G x ≠ ⊤) (hfinite : ∃ x : E, G x ≠ ⊥)
--       (a b : ℝ) (ha : 0 < a)
--       (hdecay : ∀ x : E, G x ≤ ((b - a * ‖x‖ : ℝ) : EReal)) :
--       ∃ x : E, G x ≠ ⊥ ∧ G x ≠ ⊤ ∧ ∀ z : E, G z ≤ G x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Extremum`](https://prove2.me/theorems/e7a84d99-b4b9-489a-a9b9-2b3440d6f223).
--
--   [Source excerpt, lines 23–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Extremum.lean#L23-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Extremum.lean#L20-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Extremum`, declaration `FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Extremum

theorem FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : E → EReal) (husc : UpperSemicontinuous G)
    (hnotTop : ∀ x : E, G x ≠ ⊤) (hfinite : ∃ x : E, G x ≠ ⊥)
    (a b : ℝ) (ha : 0 < a)
    (hdecay : ∀ x : E, G x ≤ ((b - a * ‖x‖ : ℝ) : EReal)) :
    ∃ x : E, G x ≠ ⊥ ∧ G x ≠ ⊤ ∧ ∀ z : E, G z ≤ G x := by sorry
