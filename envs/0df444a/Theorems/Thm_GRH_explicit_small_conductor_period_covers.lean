-- Prove2me | Theorems.Thm_GRH_explicit_small_conductor_period_covers
-- name    : GRH.explicit_small_conductor_period_covers
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:15.837782+00:00
-- url     : https://prove2.me/theorems/1b997fe3-f5cb-5d14-9300-78858c930574
-- title:
--   Arithmetic period tests up to heights one and two at small moduli
-- statement:
--   For a divisor $d$ of $8$, $12$, $18$, or $30$, the arithmetic period test passes whenever $a\ge6/7$ and $0\le H\le1$. For a divisor of $4$ or $6$, it passes throughout both ranges $a\ge1/2$, $0\le H\le1$ and $a\ge17/25$, $0\le H\le2$.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Definitions.Def_GRH_DirichletPeriod

open GRH.DirichletPeriod

theorem GRH.explicit_small_conductor_period_covers (d : ℕ) (a H : ℝ) (hH : 0 ≤ H)
    (h : ((d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30) ∧ (6/7:ℝ) ≤ a ∧ H ≤ 1) ∨
      ((d ∣ 4 ∨ d ∣ 6) ∧ (((1/2:ℝ) ≤ a ∧ H ≤ 1) ∨ ((17/25:ℝ) ≤ a ∧ H ≤ 2)))) :
    GRH.DirichletPeriod.Covers d a H := by sorry
