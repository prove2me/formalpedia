-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_theorem_3_2
-- name    : KleinbergHITS.Conv.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:32.133987+00:00
-- url     : https://prove2.me/theorems/795da435-853a-49c8-8e92-c494f87b6abb
-- title:
--   Theorem 3.2, p. 11 — under (†) the HITS iterates converge, x* to the principal eigenvector of AᵀA and y* to that of AAᵀ
-- statement:
--   Let $G$ be a directed graph on $n$ pages with adjacency matrix $A$ ($A_{ij}=1$ if page $i$ links to page $j$, else $0$), and let $(x_k,y_k)$ be the authority and hub weight vectors returned by Kleinberg's procedure Iterate$(G,k)$: starting from $x_0=y_0=(1,\dots,1)$, each round replaces the authority weight of a page by the sum of the hub weights of the pages linking to it, then the hub weight of a page by the sum of the new authority weights of the pages it links to, and normalizes both vectors so that their squares sum to $1$.
--
--   Assume Assumption (†) for $A^{\top}A$ and for $AA^{\top}$: for each of these symmetric matrices, the eigenvalue $\lambda_1$ of largest absolute value is simple, nonzero, and strictly larger in absolute value than every other eigenvalue. Then there are vectors $x^*,y^*$ such that
--   $$x_k\to x^*,\qquad y_k\to y^*\qquad(k\to\infty),$$
--   and $x^*$ is a principal eigenvector of $A^{\top}A$ and $y^*$ is a principal eigenvector of $AA^{\top}$: unit vectors with $A^{\top}Ax^*=\lambda_1(A^{\top}A)\,x^*$ and $AA^{\top}y^*=\lambda_1(AA^{\top})\,y^*$.
--
--   This is the central result of §3: the hub and authority scores computed by the HITS algorithm are the principal eigenvectors of the co-citation matrix $A^{\top}A$ and the bibliographic coupling matrix $AA^{\top}$, so that any eigenvector algorithm computes them.
--
--   **Formalization Note** Theorem 3.2 refers to the limits $x^*,y^*$ of Theorem 3.1, so the statement asserts their existence as well. Assumption (†) is the paper's standing assumption; its encoding includes $\lambda_1\ne0$, which the paper attributes to (†) on p. 11 and without which the one-page graph with no link would be a counterexample. "The principal eigenvector" is determined only up to sign; the statement says that each limit is a unit vector in the one-dimensional principal eigenspace. Non-negativity of $x^*$, $y^*$ is true but not part of the printed theorem and is not asserted.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, pp. 10–11, Theorems 3.1 and 3.2 (with Assumption (†), p. 10)

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix Filter Topology

/-- Kleinberg (1999), §3, Theorems 3.1 and 3.2, pp. 10–11: under Assumption (†) for `AᵀA` and `AAᵀ`,
the `Iterate` sequences converge to limits `x*` and `y*`, and `x*` is the principal eigenvector of
`AᵀA` and `y*` is the principal eigenvector of `AAᵀ`. -/
theorem theorem_3_2 {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAtA : Dagger ((adjMatrix E)ᵀ * adjMatrix E)) (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∃ xstar ystar : Fin n → ℝ,
      Tendsto (fun k => (hitsIter E k).1) atTop (𝓝 xstar) ∧
      Tendsto (fun k => (hitsIter E k).2) atTop (𝓝 ystar) ∧
      IsPrincipalEigenvector ((adjMatrix E)ᵀ * adjMatrix E) xstar ∧
      IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ystar := by sorry

end KleinbergHITS.Conv
