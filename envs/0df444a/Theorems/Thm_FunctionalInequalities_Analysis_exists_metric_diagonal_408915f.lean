-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_metric_diagonal_408915f
-- name    : FunctionalInequalities.Analysis.exists_metric_diagonal_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:18.468976+00:00
-- url     : https://prove2.me/theorems/5602866a-3a83-47bc-aceb-14d49bb65cdb
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/DiagonalSelector.lean#L16-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.DiagonalSelector`, declaration `FunctionalInequalities.Analysis.exists_metric_diagonal`; the repository is private at upload time).

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_metric_diagonal_408915f {X : Type*} [PseudoMetricSpace X]
    (G : ℕ → ℕ → X) (F : ℕ → X) (x : X)
    (hrow : ∀ n : ℕ, Tendsto (G n) atTop (𝓝 (F n))) (houter : Tendsto F atTop (𝓝 x)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => G n (k n)) atTop (𝓝 x) := by sorry
