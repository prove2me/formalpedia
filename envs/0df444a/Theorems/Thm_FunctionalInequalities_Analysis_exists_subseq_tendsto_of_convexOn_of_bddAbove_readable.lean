-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_subseq_tendsto_of_convexOn_of_bddAbove_readable
-- name    : FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:15.018555+00:00
-- url     : https://prove2.me/theorems/1673fa59-924b-4b3b-a359-a75c6d0c9acb
-- title:
--   Pointwise Subsequence Compactness For Nonnegative Convex Functions
-- statement:
--   This is the finite-dimensional pointwise compactness theorem for convex functions, used in the compactness argument for Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as a partial formalization.
--
--   Let $E$ be finite-dimensional over $\mathbb R$, let $K\subseteq E$ be open, and let $f_j:E\to\mathbb R$. Assume:
--
--   1. Each $f_j$ is convex on $K$.
--   2. $f_j(x)\ge0$ for every $x\in K$.
--   3. For each $x\in K$, the set $\{f_j(x):j\in\mathbb N\}$ is bounded above.
--
--   Then there exist a strictly increasing sequence $s:\mathbb N\to\mathbb N$ and a function $g:E\to\mathbb R$ such that $g$ is convex on $K$ and, for every $x\in K$,
--   $$f_{s(j)}(x)\longrightarrow g(x).$$
--
--   The conclusion also applies when $K$ is empty.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_subseq_tendsto_of_convexOn_of_bddAbove {K : Set E} (hK : IsOpen K)
--       (f : ℕ → E → ℝ) (hf : ∀ ℓ, ConvexOn ℝ K (f ℓ)) (hnn : ∀ ℓ, ∀ x ∈ K, 0 ≤ f ℓ x)
--       (hbdd : ∀ x ∈ K, BddAbove (Set.range fun ℓ => f ℓ x)) :
--       ∃ (s : ℕ → ℕ) (g : E → ℝ), StrictMono s ∧ ConvexOn ℝ K g ∧
--         ∀ x ∈ K, Filter.Tendsto (fun j => f (s j) x) Filter.atTop (nhds (g x))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/PointwiseCompactness`](https://prove2.me/theorems/566d2f2b-855b-42e3-83d2-9a81960cbc41).
--
--   [Source excerpt, lines 132–136](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/PointwiseCompactness.lean#L132-L136) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/PointwiseCompactness.lean#L130-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.PointwiseCompactness`, declaration `FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_PointwiseCompactness

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove_readable {K : Set E} (hK : IsOpen K)
    (f : ℕ → E → ℝ) (hf : ∀ ℓ, ConvexOn ℝ K (f ℓ)) (hnn : ∀ ℓ, ∀ x ∈ K, 0 ≤ f ℓ x)
    (hbdd : ∀ x ∈ K, BddAbove (Set.range fun ℓ => f ℓ x)) :
    ∃ (s : ℕ → ℕ) (g : E → ℝ), StrictMono s ∧ ConvexOn ℝ K g ∧
      ∀ x ∈ K, Filter.Tendsto (fun j => f (s j) x) Filter.atTop (nhds (g x)) := by sorry
