-- Prove2me | Theorems.Thm_JewellMRP_Discounted_qtilde_mem_Ico
-- name    : JewellMRP.Discounted.qtilde_mem_Ico
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:58:55.13617+00:00
-- url     : https://prove2.me/theorems/e6513c04-9842-4cb6-9af9-df418861161d
-- title:
--   p. 945 — every element of $\tilde q(s) = [p_{ij}\tilde f_{ij}(s)]$ lies in $[0,1)$ for $s>0$
-- statement:
--   Let a Markov-renewal program be given, with transition probabilities $p^z_{ij}$ and sojourn-time distributions $F^z_{ij}$ that give no mass to $(-\infty, 0]$, and let $\tilde f^z_{ij}(s) = \int_0^\infty e^{-st}\,dF^z_{ij}(t)$ be their Laplace–Stieltjes transforms. Then for every $s > 0$, every alternative $z$ and all states $i, j$,
--   $$
--   0 \le p^z_{ij}\,\tilde f^z_{ij}(s) < 1 .
--   $$
--
--   The paper states this on p. 945 as the reason why the returns stay finite as the horizon grows: "all elements of the matrix $\tilde q(s) = [p_{ij}\tilde f_{ij}(s)]$ lie in the interval $[0, 1)$ for all $s>0$, and for all policies". It is the elementary fact behind the solvability of the value-determination equations and the convergence of the discounted returns.
--
--   **Formalization Note** Only the "since" clause of the sentence is formalized. The finiteness of $V_i(n,\alpha)$ for each $n$ is automatic for real-valued returns, and the continuous-time returns $v_i(t,\alpha)$ of (10) are outside this mission. "For all policies" is expressed by quantifying over every alternative $z$. The strict inequality uses $F^z_{ij}(0) = 0$, part of the model.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 945, Discounted Models with Infinite Step or Time Horizons

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

namespace JewellMRP.Discounted

/-- p. 945: every element of `q̃(s) = [p^z_{ij} f̃^z_{ij}(s)]` lies in `[0, 1)` for `s > 0`,
for every alternative `z`. -/
theorem qtilde_mem_Ico {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : qtilde M s z i j ∈ Set.Ico 0 1 := by sorry

end JewellMRP.Discounted
