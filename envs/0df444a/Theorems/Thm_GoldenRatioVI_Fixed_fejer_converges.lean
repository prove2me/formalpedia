-- Prove2me | Theorems.Thm_GoldenRatioVI_Fixed_fejer_converges
-- name    : GoldenRatioVI.Fixed.fejer_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:58:02.941999+00:00
-- url     : https://prove2.me/theorems/4064b35c-2b34-490a-ae8e-6e7d7d0d4b27
-- title:
--   Lemma 1 — Fejér monotone sequences with cluster points in $C$ converge to a point of $C$
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space, $(z^k)\subset\mathcal E$ and $C\subseteq\mathcal E$ a nonempty set. Suppose that $(z^k)$ is **Fejér monotone** with respect to $C$,
--   $$\|z^{k+1}-z\| \le \|z^k - z\| \qquad \text{for all } z\in C \text{ and all } k,$$
--   and that every cluster point of $(z^k)$ belongs to $C$. Then $(z^k)$ converges to a point of $C$.
--
--   This is the standard device (Bauschke–Combettes, Theorem 5.5) that turns the energy decrease and the identification of cluster points into convergence of the whole sequence.
--
--   **Formalization Note** The paper states the lemma for an arbitrary $C\subseteq\mathcal E$; it is false for $C=\emptyset$ (both hypotheses hold vacuously for $z^k = k v$ with $v\ne0$), and Bauschke–Combettes assume $C\neq\emptyset$. The hypothesis $C\ne\emptyset$ is therefore added. A cluster point is a point $x$ with `MapClusterPt x atTop z`.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 3, Lemma 1 (Theorem 5.5 in Bauschke–Combettes)

import Mathlib

namespace GoldenRatioVI.Fixed

/-- Lemma 1 (Bauschke–Combettes, Thm 5.5): in a finite-dimensional real inner product space,
if `(zᵏ)` is Fejér monotone w.r.t. a nonempty set `C` (`‖zᵏ⁺¹ - z‖ ≤ ‖zᵏ - z‖` for all `z ∈ C`)
and every cluster point of `(zᵏ)` lies in `C`, then `(zᵏ)` converges to a point of `C`.
The hypothesis `C.Nonempty` is not printed in the paper; the statement is false without it. -/
theorem fejer_converges {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : ℕ → E) (C : Set E) (hC : C.Nonempty)
    (hfejer : ∀ k : ℕ, ∀ c ∈ C, ‖z (k + 1) - c‖ ≤ ‖z k - c‖)
    (hclust : ∀ x : E, MapClusterPt x Filter.atTop z → x ∈ C) :
    ∃ x ∈ C, Filter.Tendsto z Filter.atTop (nhds x) := by sorry

end GoldenRatioVI.Fixed
