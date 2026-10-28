-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_metric_diagonal_readable
-- name    : FunctionalInequalities.Analysis.exists_metric_diagonal_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:18.185985+00:00
-- url     : https://prove2.me/theorems/c1baf226-693c-4f22-b2f1-ccc4640d1cd9
-- title:
--   Metric Diagonal Selection
-- statement:
--   This is a generic diagonal-selection theorem in a pseudometric space.
--
--   Let $X$ be a pseudometric space, let $G:\mathbb N\to\mathbb N\to X$, let $F:\mathbb N\to X$, and let $x\in X$. Assume that for every $n$, $G(n,k)\to F(n)$ as $k\to\infty$, and that $F(n)\to x$ as $n\to\infty$. Then there exists $k:\mathbb N\to\mathbb N$ such that
--
--   $$n\le k(n),\qquad k(n)\to\infty,
--   \qquad G(n,k(n))\to x.$$
--
--   This provides a reusable diagonalization tool for joint limiting constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_metric_diagonal {X : Type*} [PseudoMetricSpace X]
--       (G : ℕ → ℕ → X) (F : ℕ → X) (x : X)
--       (hrow : ∀ n : ℕ, Tendsto (G n) atTop (𝓝 (F n))) (houter : Tendsto F atTop (𝓝 x)) :
--       ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
--         Tendsto (fun n => G n (k n)) atTop (𝓝 x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/DiagonalSelector`](https://prove2.me/theorems/7adcdbd1-7f86-49e3-a792-dc6701cfeaf2).
--
--   [Source excerpt, lines 18–22](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/DiagonalSelector.lean#L18-L22) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/DiagonalSelector.lean#L16-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.DiagonalSelector`, declaration `FunctionalInequalities.Analysis.exists_metric_diagonal`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_DiagonalSelector

open Filter Topology

theorem FunctionalInequalities.Analysis.exists_metric_diagonal_readable {X : Type*} [PseudoMetricSpace X]
    (G : ℕ → ℕ → X) (F : ℕ → X) (x : X)
    (hrow : ∀ n : ℕ, Tendsto (G n) atTop (𝓝 (F n))) (houter : Tendsto F atTop (𝓝 x)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => G n (k n)) atTop (𝓝 x) := by sorry
