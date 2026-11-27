-- Prove2me | Theorems.Thm_LinearChoresCLS_epsQKKT_short_rational
-- name    : LinearChoresCLS.epsQKKT_short_rational
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:02:31.900256+00:00
-- url     : https://prove2.me/theorems/1f86f9fc-07d8-5d5e-9568-1b53b43358f3
-- title:
--   Short rational $\varepsilon$-KKT points of box quadratic programs exist
-- statement:
--   This is the totality part of the membership of the $\varepsilon$-quadratic-KKT problem in TFNP.
--
--   An instance consists of a symmetric rational matrix $A\in\mathbb Q^{n\times n}$ with $n\ge1$, a rational vector $c\in\mathbb Q^n$ and a rational $\varepsilon>0$, written as the code $x=\mathrm{enc}(A,c)\,\mathrm{enc}(\varepsilon)$. A point $z\in[0,1]^n$ is an $\varepsilon$-KKT point of the box quadratic program $\max\{Q(z)=\tfrac12 z^\top Az+c^\top z : z\in[0,1]^n\}$ if for every coordinate $i$, with $g_i=(Az+c)_i$,
--
--   $$z_i=0\Rightarrow g_i\le\varepsilon,\qquad 0<z_i<1\Rightarrow |g_i|\le\varepsilon,\qquad z_i=1\Rightarrow g_i\ge-\varepsilon .$$
--
--   The statement asserts that there is one exponent $k$ such that every instance $x$ has a rational $\varepsilon$-KKT point $z$ whose code satisfies
--
--   $$|\mathrm{enc}(z)|\le(|x|+1)^k+k .$$
--
--   Together with polynomial-time checkability and a reduction to 3D-Continuous-Localopt, it gives the CLS membership half of Theorem 2.5.
--
--   **Formalization Note** The search problem is `LinearChoresCLS.epsQKKTSearch` and the answer-length bound is the public `bounded`; `TotalSearch` is the public totality predicate of `NetworkEquilibriumCLS.LinearNash`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589, Theorem 2.5 (p.7, citing Fearnley–Goldberg–Hollender–Savani, STOC 2024, Theorem 2.1 and Lemma A.1) and Definition 2.4 (p.7); membership in CLS as defined through TFNP and 3D-Continuous-Localopt (Daskalakis–Papadimitriou 2011; FGHS, JACM 2023, Definition 4).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsQKKT_short_rational :
    ∃ k : ℕ, TotalSearch (bounded LinearChoresCLS.epsQKKTSearch k) := by sorry
