-- Prove2me | Theorems.Thm_LinearChoresCLS_epsQKKT_cls_reduction
-- name    : LinearChoresCLS.epsQKKT_cls_reduction
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:02:31.217811+00:00
-- url     : https://prove2.me/theorems/b23bf12a-5f2f-515a-b119-e1bcb9738ecf
-- title:
--   $\varepsilon$-quadratic-KKT reduces to 3D-Continuous-Localopt
-- statement:
--   This is the reduction part of the CLS membership of the $\varepsilon$-quadratic-KKT problem (Theorem 2.5).
--
--   For every fixed $k$, the search problem "given a box quadratic program $\max\{\tfrac12z^\top Az+c^\top z : z\in[0,1]^n\}$ with symmetric rational $A$, rational $c$ and rational $\varepsilon>0$, find a rational $\varepsilon$-KKT point $z$ with $|\mathrm{enc}(z)|\le(|x|+1)^k+k$" admits a polynomial-time Levin reduction to the canonical CLS-complete problem 3D-Continuous-Localopt: instances map to instances in polynomial time, and every solution of the image instance is mapped back, in polynomial time, to an answer of the original instance.
--
--   Together with totality and polynomial-time checkability it yields membership of the problem in CLS.
--
--   **Formalization Note** `SearchReduces` is the public Levin reduction on Cook's machines and `clsSearch` is the public canonical 3D-Continuous-Localopt (one shared circuit, max norm, both Lipschitz-violation witnesses).
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589, Theorem 2.5 (p.7, citing Fearnley–Goldberg–Hollender–Savani, STOC 2024, Theorem 2.1 and Lemma A.1) and Definition 2.4 (p.7); membership in CLS as defined through TFNP and 3D-Continuous-Localopt (Daskalakis–Papadimitriou 2011; FGHS, JACM 2023, Definition 4).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsQKKT_cls_reduction (k : ℕ) :
    SearchReduces (bounded LinearChoresCLS.epsQKKTSearch k) clsSearch := by sorry
