-- Prove2me | Theorems.Thm_LinearChoresCLS_epsQKKT_cls_membership
-- name    : LinearChoresCLS.epsQKKT_cls_membership
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:46.900798+00:00
-- url     : https://prove2.me/theorems/9adb6a1a-1ede-4f21-9f9f-431210d89802
-- title:
--   Theorem 2.5 (membership) — bounded $\varepsilon$-quadratic-KKT lies in CLS
-- statement:
--   The bounded $\varepsilon$-quadratic-KKT problem belongs to $\mathrm{CLS}$. There is one exponent $k$, fixed independently of the instance, such that the search problem accepting exactly the rational $\varepsilon$-KKT points of encoding length at most $(|I|+1)^k+k$ is in $\mathrm{TFNP}$ and reduces to 3D-Continuous-Localopt:
--   $$
--   \exists k\in\mathbb N,\qquad \operatorname{bounded}(\varepsilon\text{-quadratic-KKT},k)\in\mathrm{CLS}.
--   $$
--   This membership half of Theorem 2.5 includes totality, the uniform rational-answer bound, polynomial-time verification, and the canonical CLS reduction.
--
--   **Formalization Note** CLS membership and the answer restriction are the public `InCLS` and `bounded` predicates.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 2.5, p.7; Fearnley–Goldberg–Hollender–Savani 2024, Theorem 2.1 and Lemma A.1 (membership).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsQKKT_cls_membership : ∃ k : ℕ, NetworkEquilibriumCLS.LinearNash.InCLS (NetworkEquilibriumCLS.LinearNash.bounded epsQKKTSearch k) := by sorry
