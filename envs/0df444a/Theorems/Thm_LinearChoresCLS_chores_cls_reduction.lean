-- Prove2me | Theorems.Thm_LinearChoresCLS_chores_cls_reduction
-- name    : LinearChoresCLS.chores_cls_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:17.033278+00:00
-- url     : https://prove2.me/theorems/7a527381-9cfe-44d5-8e77-18fa8456d2b0
-- title:
--   Bounded linear chores CE reduces to 3D-Continuous-Localopt
-- statement:
--   For every fixed answer-length exponent $k$, the problem of finding an exact rational competitive equilibrium of a valid rational linear Fisher market with chores, with answers bounded by $(|x|+1)^k+k$, admits a polynomial-time Levin search reduction to the canonical 3D-Continuous-Localopt problem.
--
--   Thus, once short answers and polynomial-time verification are established, the bounded problem belongs to CLS. This is the reduction component of the cited membership in $\mathrm{PPAD}\cap\mathrm{PLS}=\mathrm{CLS}$.
--
--   **Formalization Note** `SearchReduces` supplies polynomial-time instance and answer maps on Cook's machines and requires correctness for every answer of the target CLS instance.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e…), pp.3–4, citing Chaudhury–Garg–McGlaughlin–Mehta 2022 and CLS = PPAD ∩ PLS from Fearnley–Goldberg–Hollender–Savani 2023.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

/-- The bounded exact linear-chores equilibrium search problem reduces in polynomial time to the
canonical three-dimensional Continuous-Localopt problem. -/
theorem LinearChoresCLS.chores_cls_reduction (k : ℕ) :
    SearchReduces (bounded choresCESearch k) clsSearch := by sorry
