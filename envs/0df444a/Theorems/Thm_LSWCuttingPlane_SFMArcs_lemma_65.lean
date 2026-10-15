-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_lemma_65
-- name    : LSWCuttingPlane.SFMArcs.lemma_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:41.489843+00:00
-- url     : https://prove2.me/theorems/817132aa-7b78-4b0c-a7fb-d10ef50a2fce
-- title:
--   Lemma 65, p. 77 — a non-negative h ∈ B(f) makes ∅ a minimizer, a non-positive one makes V a minimizer
-- statement:
--   Let $f : 2^V \to \mathbb Z$ be a submodular function on $V = [n]$ with $f(\emptyset) = 0$, and let $h \in \mathcal B(f)$ be a vector of its base polyhedron. Then:
--
--   1. if $h \ge 0$ entrywise, $\emptyset$ is a minimizer of $f$: $f(\emptyset) \le f(S)$ for all $S \subseteq V$;
--   2. if $h \le 0$ entrywise, $V$ is a minimizer of $f$: $f(V) \le f(S)$ for all $S \subseteq V$.
--
--   $$h \ge 0 \Rightarrow \emptyset \in \arg\min_{S \subseteq V} f(S), \qquad h \le 0 \Rightarrow V \in \arg\min_{S \subseteq V} f(S).$$
--
--   These degenerate points of the base polyhedron solve submodular minimization outright, which is why the later lemmas assume non-degeneracy.
--
--   **Formalization Note** The minimizer is over all subsets of $V$, as in §13.3 (before ring families are introduced). The normalization $f(\emptyset) = 0$ and the submodularity of $f$ are the standing assumptions of §13.1 ("throughout the rest of the paper … f … submodular"); the proof on p. 77 uses only the former.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 77, Lemma 65

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Lemma 65 (Degenerate Hyperplanes), p. 77: if `h ∈ B(f)` is non-negative then `∅` is a
minimizer of `f`, and if `h` is non-positive then `V` is a minimizer of `f` (over all subsets
of `V`). -/
theorem lemma_65 {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (h : Fin n → ℝ) (hB : h ∈ baseB f) :
    ((∀ i, 0 ≤ h i) → ∀ S : Finset (Fin n), f ∅ ≤ f S) ∧
    ((∀ i, h i ≤ 0) → ∀ S : Finset (Fin n), f Finset.univ ≤ f S) := by sorry

end LSWCuttingPlane.SFMArcs
