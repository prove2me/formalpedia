-- Prove2me | Theorems.Thm_LinearChoresCLS_epsQKKT_cls_reduction_eventually
-- name    : LinearChoresCLS.epsQKKT_cls_reduction_eventually
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:41:55.518936+00:00
-- url     : https://prove2.me/theorems/119e304b-9c34-54df-ae6a-92996ed410f0
-- title:
--   $\varepsilon$-quadratic-KKT reduces to 3D-Continuous-Localopt for all large answer bounds
-- statement:
--   There is a threshold $K$ such that, for every answer-length exponent $k\ge K$, the $\varepsilon$-quadratic-KKT search problem (Definition 2.4) reduces in polynomial time to the canonical 3D-Continuous-Localopt problem `clsSearch`. Here an answer for an instance $x$ must have encoding length at most $(|x|+1)^k+k$. Formally,
--
--   $$\exists K\ \forall k\ge K:\quad \mathrm{SearchReduces}\big(\mathrm{bounded}(\varepsilon\text{-}\textsc{QKKT},k),\ \texttt{clsSearch}\big).$$
--
--   This is the reduction component of the cited membership of $\varepsilon$-quadratic-KKT in CLS (Fearnley–Goldberg–Hollender–Savani, via $\mathrm{PPAD}\cap\mathrm{PLS}=\mathrm{CLS}$). Combined with short rational answers and polynomial-time checking, it gives $\exists k,\ \mathrm{InCLS}(\mathrm{bounded}(\varepsilon\text{-}\textsc{QKKT},k))$.
--
--   **Formalization Note** It corrects the disproved `LinearChoresCLS.epsQKKT_cls_reduction`, which asserted the reduction for every $k$. For $k=0$ no answer fits the length bound $1$, while `clsSearch` is total.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e…), Theorem 2.5 (p.7) and Definition 2.4 (p.7), citing Fearnley–Goldberg–Hollender–Savani (arXiv:2011.01929, J. ACM 2022, Section 1.2: CLS = PPAD ∩ PLS; high-dimensional KKT lies in CLS).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsQKKT_cls_reduction_eventually :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → SearchReduces (bounded LinearChoresCLS.epsQKKTSearch k) clsSearch := by sorry
