-- Prove2me | Theorems.Thm_Hirsch_larman_dimension_step
-- name    : Hirsch.larman_dimension_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:52.000572+00:00
-- url     : https://prove2.me/theorems/2b8d4432-69ac-4610-9194-f448c6e47bc8
-- title:
--   Larman's dimension step: $\Delta(d+1,n)\le 2^{d-2}n-1$ from $\Delta(d,m)\le 2^{d-3}m-1$
-- statement:
--   Let $d\ge3$ and suppose that every nonempty bounded H-polytope in $\mathbb{R}^{d}$ described by $m$ inequalities has combinatorial diameter at most $2^{d-3}m-1$, for every $m$. Then every nonempty bounded H-polytope $P\subseteq\mathbb{R}^{d+1}$ described by $n$ inequalities satisfies
--
--   $$\operatorname{DiamLE}\bigl(P,\ 2^{d-2}\,n-1\bigr).$$
--
--   This is one rung of Larman's induction on the dimension. Its proof is the layer decomposition `Hirsch.larman_layer_recursion` with $\beta(m)=2^{d-3}m-1$ and $B_{d+1}=2^{d-2}n-1$: the facets of $P$ are $d$-dimensional, the relaxation of a facet to the $m_i$ rows active in the $i$-th layer has diameter at most $\beta(m_i)$ by hypothesis (via `Hirsch.larman_layer_step`), and the arithmetic condition reads $\sum_i(2^{d-3}m_i-1)+k=2^{d-3}\sum_i m_i\le 2^{d-3}\cdot2n=2^{d-2}n$. Rows with zero normal are removed first by `Hirsch.diamLE_of_nonzero_rows`. Together with Klee's theorem $\Delta(3,n)\le n-3$ as the base case, iterating this step gives Larman's bound $\Delta(d,n)\le2^{d-3}n$ for all $d\ge3$.
--
--   **Formalization Note** Subtraction is truncated natural subtraction; since $m\ge1$ for every description that has a vertex and $2^{d-3}\ge1$, the bounds $2^{d-3}m-1$ are exact. The invariant with the "$-1$" is slightly sharper than the milestone's $n\cdot2^{d-3}$ and is what the sum telescopes to; the milestone follows by padding.
-- source:
--   D. G. Larman, Paths on polytopes, Proc. London Math. Soc. s3-20 (1970) 161-178, https://doi.org/10.1112/plms/s3-20.2.249; exposition followed: E. D. Kim, F. Santos, Companion to 'An update on the Hirsch conjecture', arXiv:0912.4235, Section 2.2, proof of Theorem 2.5 (layer decomposition, 'no facet is active in more than two V_i's', sum n_i <= 2n); F. Santos, TOP 21 (2013), arXiv:1307.5900, Lemma 3.13 and Theorem 3.14. Base case: V. Klee, Diameters of polyhedral graphs, Canad. J. Math. 16 (1964) 602-614 (Prove2Me Hirsch.klee_three_dimensional_bound, 74a8218d-aaa5-48f3-b993-37445f2c7013).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem larman_dimension_step (d n : ℕ) (hd : 3 ≤ d)
    (IH : ∀ (m : ℕ) (a' : Fin m → EuclideanSpace ℝ (Fin d)) (b' : Fin m → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') (2 ^ (d - 3) * m - 1))
    (a : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (2 ^ (d - 2) * n - 1) := by sorry

end Hirsch
