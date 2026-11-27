-- Prove2me | Theorems.Thm_LinearChoresCLS_epsQKKT_checkable
-- name    : LinearChoresCLS.epsQKKT_checkable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:02:38.552079+00:00
-- url     : https://prove2.me/theorems/8fe65665-6fe9-4ec0-8672-0546cae54233
-- title:
--   $\varepsilon$-KKT points of box quadratic programs are polynomial-time checkable
-- statement:
--   This is the verification part of the membership of the $\varepsilon$-quadratic-KKT problem in TFNP.
--
--   Fix $k\in\mathbb N$. Consider pairs $(x,y)$ of bit strings where $x=\mathrm{enc}(A,c)\,\mathrm{enc}(\varepsilon)$ encodes a box quadratic program with symmetric $A\in\mathbb Q^{n\times n}$, $n\ge1$, $c\in\mathbb Q^n$ and $\varepsilon>0$, and $y=\mathrm{enc}(z)$ encodes a rational $\varepsilon$-KKT point $z\in[0,1]^n$ (Definition 2.4, maximization signs) with $|y|\le(|x|+1)^k+k$. The statement asserts that the language $\{x\#y\}$ of such pairs belongs to Cook's class $\mathrm P$ over the alphabet $\{0,1\}\sqcup\{0,1\}\sqcup\{\#\}$.
--
--   It is the polynomial-time checkability condition in the definition of TFNP used by the public `InCLS`.
--
--   **Formalization Note** `CookPvsNP.checkLang` and `CookPvsNP.P` are the public notions on Cook's one-tape machines.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589, Theorem 2.5 (p.7, citing Fearnley–Goldberg–Hollender–Savani, STOC 2024, Theorem 2.1 and Lemma A.1) and Definition 2.4 (p.7); membership in CLS as defined through TFNP and 3D-Continuous-Localopt (Daskalakis–Papadimitriou 2011; FGHS, JACM 2023, Definition 4).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsQKKT_checkable (k : ℕ) :
    CookPvsNP.checkLang (fun x y => (bounded LinearChoresCLS.epsQKKTSearch k).valid x ∧
      (bounded LinearChoresCLS.epsQKKTSearch k).answer x y) ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry
