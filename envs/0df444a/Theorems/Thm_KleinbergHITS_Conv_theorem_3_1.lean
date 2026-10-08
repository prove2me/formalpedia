-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_theorem_3_1
-- name    : KleinbergHITS.Conv.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:12.813333+00:00
-- url     : https://prove2.me/theorems/0ee732ad-3f69-46b2-b963-7e0900cf2755
-- title:
--   Theorem 3.1, p. 10 — the HITS iterates x₁, x₂, … and y₁, y₂, … converge
-- statement:
--   Let $G$ be a directed graph on $n$ pages with adjacency matrix $A$, and let $(x_k,y_k)$ be the authority and hub weight vectors returned by Iterate$(G,k)$ (start from the all-ones vector, alternately apply the $\mathcal I$ and $\mathcal O$ operations, and normalize so that the squares sum to $1$). Assume the standing Assumption (†) for both $A^{\top}A$ and $AA^{\top}$. Then both sequences converge: there are vectors $x^*,y^*\in\mathbb R^n$ with
--   $$x_k\to x^*,\qquad y_k\to y^*\qquad(k\to\infty).$$
--
--   This justifies running Iterate for a large number of rounds: the weights stabilize at fixed points, whose identification is Theorem 3.2.
--
--   **Formalization Note** The printed theorem has no hypothesis; Assumption (†) is the standing assumption of p. 10 ("we will make the following technical assumption about all the matrices we deal with") and its proof uses it, so it appears as two hypotheses, one per matrix. Convergence is in $\mathbb R^n$ (all norms agree). The page's sequence starts at $x_1$; the Lean sequence starts at $x_0$, which does not affect convergence.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 10, Theorem 3.1 (with Assumption (†), p. 10)

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix Filter Topology

/-- Kleinberg (1999), §3, Theorem 3.1, p. 10: under the standing Assumption (†) for `AᵀA` and `AAᵀ`,
the sequences `x₁, x₂, x₃, …` and `y₁, y₂, y₃, …` produced by `Iterate` converge. -/
theorem theorem_3_1 {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAtA : Dagger ((adjMatrix E)ᵀ * adjMatrix E)) (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    (∃ xstar : Fin n → ℝ, Tendsto (fun k => (hitsIter E k).1) atTop (𝓝 xstar)) ∧
      (∃ ystar : Fin n → ℝ, Tendsto (fun k => (hitsIter E k).2) atTop (𝓝 ystar)) := by sorry

end KleinbergHITS.Conv
