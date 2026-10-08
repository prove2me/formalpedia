-- Prove2me | Theorems.Thm_MDPComplexity_Discounted_B_cheapest_walk
-- name    : MDPComplexity.Discounted.B_cheapest_walk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:17.560499+00:00
-- url     : https://prove2.me/theorems/05b5a11a-80b6-49f9-88ad-ccbeb89a3217
-- title:
--   §3, discounted case (p. 447) — the min-plus products B_j are the cheapest discounted j-arc walks
-- statement:
--   Let $0<\beta<1$, and let $B_j=A\otimes\beta A\otimes\cdots\otimes\beta^{j-1}A$ be the min-plus product of the scaled cost matrices of a finite deterministic Markov decision process ($B_0$ the min-plus identity). For all $j\ge0$ and states $u,v$:
--
--   1. $(B_j)_{uv}=+\infty$ if and only if there is no walk with $j$ arcs from $u$ to $v$;
--   2. otherwise $(B_j)_{uv}$ is a real number, and it is the least discounted length
--   $$\min_{W}\ \sum_{t=0}^{j-1}\beta^t c(w_t,e_t)$$
--   over all $j$-arc walks $W=(w_0=u,e_0,w_1,\dots,e_{j-1},w_j=v)$, the minimum being attained.
--
--   This is what makes the matrix products compute "the shortest discounted path" with a prescribed number of arcs; the arcs of a walk may repeat nodes, and parallel decisions contribute their cheapest one.
--
--   **Formalization Note** The paper says "the $(u,v)$th entry of $B_j$ is the length of the shortest path with $j$ arcs from $u$ to $v$" in the sense of the discounted length (the $t$-th arc weighted by $\beta^t$). We define $B_j$ as the matrix product and state its walk interpretation here. Entries are in `Tropical (WithTop ℝ)`; `trop ⊤` is $+\infty$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 446–447, §3, The infinite horizon, discounted case

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

namespace MDPComplexity.Discounted

theorem B_cheapest_walk {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) (j : ℕ) (u v : S) :
    (M.B β j u v = Tropical.trop (⊤ : WithTop ℝ) ↔ IsEmpty (M.Walk j u v)) ∧
    ∀ W : M.Walk j u v, ∃ x : ℝ, M.B β j u v = Tropical.trop (x : WithTop ℝ) ∧
      IsLeast (Set.range fun W' : M.Walk j u v => W'.cost β) x := by sorry

end MDPComplexity.Discounted
