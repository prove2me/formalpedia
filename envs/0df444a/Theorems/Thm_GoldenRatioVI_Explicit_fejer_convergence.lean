-- Prove2me | Theorems.Thm_GoldenRatioVI_Explicit_fejer_convergence
-- name    : GoldenRatioVI.Explicit.fejer_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:31:57.546518+00:00
-- url     : https://prove2.me/theorems/5c25a46e-6ddc-4081-a704-4262a6798f76
-- title:
--   Lemma 1 — Fejér monotone sequences with cluster points in C converge to a point of C
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space, let $C\subseteq\mathcal E$ be nonempty and let $(z^k)\subset\mathcal E$. Suppose that $(z^k)$ is **Fejér monotone** with respect to $C$,
--   $$\|z^{k+1}-z\|\le\|z^k-z\|\qquad\text{for all } z\in C \text{ and all } k,$$
--   and that every cluster point of $(z^k)$ belongs to $C$. Then $(z^k)$ converges to a point of $C$.
--
--   This is the final step of the convergence proofs of the paper: once the iterates are shown to be Fejér monotone (for a suitable energy) with respect to the solution set and all their cluster points are solutions, the whole sequence converges.
--
--   **Formalization Note** The paper quotes the lemma from Bauschke–Combettes (Theorem 5.5) without the hypothesis $C\neq\emptyset$, which the cited source has; without it the statement is false (take $C=\emptyset$ and $z^k = k\,e$ for a unit vector $e$). The hypothesis is added.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 3, Lemma 1 (quoting Bauschke–Combettes, Theorem 5.5)

import Mathlib
open Filter Topology

namespace GoldenRatioVI.Explicit

/-- Lemma 1 of Malitsky (p. 3), quoting Bauschke–Combettes, Theorem 5.5: in a
finite-dimensional inner product space, let `C` be a nonempty set and `(z^k)` a sequence that is
Fejér monotone w.r.t. `C` (`‖z^{k+1} − c‖ ≤ ‖z^k − c‖` for all `c ∈ C` and all `k`) and whose
cluster points all lie in `C`. Then `(z^k)` converges to a point of `C`. (`C ≠ ∅` is assumed
in Bauschke–Combettes and dropped in the quotation; without it the lemma is false.) -/
theorem fejer_convergence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : ℕ → E) (C : Set E) (hC : C.Nonempty)
    (hfejer : ∀ c ∈ C, ∀ k : ℕ, ‖z (k + 1) - c‖ ≤ ‖z k - c‖)
    (hclus : ∀ x : E, MapClusterPt x atTop z → x ∈ C) :
    ∃ x ∈ C, Tendsto z atTop (𝓝 x) := by sorry

end GoldenRatioVI.Explicit
