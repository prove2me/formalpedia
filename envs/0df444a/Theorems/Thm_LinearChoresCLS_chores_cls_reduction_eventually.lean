-- Prove2me | Theorems.Thm_LinearChoresCLS_chores_cls_reduction_eventually
-- name    : LinearChoresCLS.chores_cls_reduction_eventually
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:41:58.011051+00:00
-- url     : https://prove2.me/theorems/e0a0a2cf-8e5b-4d5f-af14-3262a1f6ad2f
-- title:
--   Linear-chores CE reduces to 3D-Continuous-Localopt for all large answer bounds
-- statement:
--   There is a threshold $K$ such that, for every answer-length exponent $k\ge K$, the problem of finding an exact rational competitive equilibrium of a valid rational linear Fisher market with chores reduces in polynomial time to the canonical 3D-Continuous-Localopt problem `clsSearch`. Here an answer for an instance $x$ must have encoding length at most $(|x|+1)^k+k$. Formally,
--
--   $$\exists K\ \forall k\ge K:\quad \mathrm{SearchReduces}\big(\mathrm{bounded}(\textsc{ChoresCE},k),\ \texttt{clsSearch}\big).$$
--
--   This is the reduction component of the cited membership of the problem in $\mathrm{PPAD}\cap\mathrm{PLS}=\mathrm{CLS}$. Combined with short rational equilibria and polynomial-time checking, it gives $\exists k,\ \mathrm{InCLS}(\mathrm{bounded}(\textsc{ChoresCE},k))$ by taking $k$ at least both thresholds.
--
--   **Formalization Note** It corrects the disproved `LinearChoresCLS.chores_cls_reduction`, which asserted the reduction for **every** $k$. For $k=0$ the bound $(|x|+1)^0+0=1$ admits no answer at all, while `clsSearch` is total, so no reduction can exist. Only sufficiently large $k$ is meaningful.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e…), pp.3–4 (membership in CLS), citing Chaudhury–Garg–McGlaughlin–Mehta 2022 and CLS = PPAD ∩ PLS from Fearnley–Goldberg–Hollender–Savani (arXiv:2011.01929, J. ACM 2022, Section 1.2).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.chores_cls_reduction_eventually :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → SearchReduces (bounded LinearChoresCLS.choresCESearch k) clsSearch := by sorry
