-- Prove2me | Theorems.Thm_MatousekLP_DIntervals_exists_endpoint_weights
-- name    : MatousekLP.DIntervals.exists_endpoint_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:02:08.869558+00:00
-- url     : https://prove2.me/theorems/6c3397ef-0214-4e5e-8bdd-e6ef7a02cbb8
-- title:
--   Lemma 8.6.3 — weights on the endpoints of total at most 2d giving every d-interval weight ≥ 1
-- statement:
--   Let $d \ge 1$, let $\mathcal J$ be a finite family of pairwise intersecting $d$-intervals, and let $P$ be the set of endpoints of the $d$-intervals in $\mathcal J$. Then there are nonnegative real numbers $x_p$, $p \in P$, such that
--   $$
--   \sum_{p \in J \cap P} x_p \;\ge\; 1 \ \text{ for every } J \in \mathcal J, \qquad\text{and}\qquad \sum_{p \in P} x_p \;\le\; 2d .
--   $$
--
--   In the language of set systems: the family $\mathcal J$, restricted to the finite ground set $P$, has fractional transversal number at most $2d$. Together with a left-to-right selection of points this yields the $2d^2$ transversal of Theorem 8.6.1.
--
--   **Formalization Note** The weights are a function $x : \mathbb R \to \mathbb R$ of which only the values on $P$ matter; nonnegativity is required on $P$. $J \cap P$ is the set of endpoints (of any member of $\mathcal J$) lying in the set $J$. Endpoints are those of the component intervals of each $d$-interval's representation.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 179, Lemma 8.6.3

import Mathlib
import Definitions.Def_MatousekLP_DIntervals_DInterval

open Finset

namespace MatousekLP.DIntervals

open Classical in
/-- Lemma 8.6.3 (p. 179): for a finite family `𝒥` of pairwise intersecting `d`-intervals with
endpoint set `P`, there are weights `x_p ≥ 0`, `p ∈ P`, with `Σ_{p ∈ J ∩ P} x_p ≥ 1` for every
`J ∈ 𝒥` and `Σ_{p ∈ P} x_p ≤ 2d`. The weights are a function `ℝ → ℝ`; only its values on `P`
matter. -/
theorem exists_endpoint_weights {d : ℕ} (hd : 1 ≤ d) (𝒥 : Finset (DInterval d))
    (h𝒥 : PairwiseIntersecting 𝒥) :
    ∃ x : ℝ → ℝ, (∀ p ∈ endpointSet 𝒥, 0 ≤ x p) ∧
      (∀ J ∈ 𝒥, 1 ≤ ∑ p ∈ (endpointSet 𝒥).filter (fun p => p ∈ J.toSet), x p) ∧
      ∑ p ∈ endpointSet 𝒥, x p ≤ 2 * d := by sorry

end MatousekLP.DIntervals
