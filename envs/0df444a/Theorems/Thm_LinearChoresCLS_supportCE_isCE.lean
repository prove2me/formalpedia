-- Prove2me | Theorems.Thm_LinearChoresCLS_supportCE_isCE
-- name    : LinearChoresCLS.supportCE_isCE
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:45.86548+00:00
-- url     : https://prove2.me/theorems/3a4a5022-ea5f-46f6-a515-c461de47b5d6
-- title:
--   Complementary support certificates imply competitive equilibrium
-- statement:
--   Every finite support certificate for a linear chores market is a competitive equilibrium.
--
--   Concretely, suppose $p,z\ge0$, $\nu_a\ge0$, every agent earns exactly $B_a$, every chore clears, and
--   $$
--   \nu_a p_j\le d_{aj}\quad\text{for all }a,j,
--   \qquad z_{aj}>0\implies \nu_a p_j=d_{aj}.
--   $$
--   Then each $z_a$ belongs to the demand set $X_a(p)$, so $(p,z)$ is a competitive equilibrium. The statement needs no positivity or market-validity hypothesis beyond what is included in the support system.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589, Definitions 2.1–2.2 and the displayed ratio characterization of individual optimality, p.6.

import Mathlib
import Definitions.Def_LinearChoresCLS_SupportCE

open scoped BigOperators
open Finset

theorem LinearChoresCLS.supportCE_isCE {N M : Type*} [Fintype N] [Fintype M]
    {F : ChoresMarket N M} {p : M → ℝ} {ν : N → ℝ} {z : N → M → ℝ}
    (h : F.SupportCE p ν z) : F.IsCE p z := by sorry
