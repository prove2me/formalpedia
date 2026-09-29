-- Prove2me | Theorems.Thm_Nat_macaulayPow_lt_macaulayPow_of_lt
-- name    : Nat.macaulayPow_lt_macaulayPow_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/704f5d6b-99e5-5dc2-98b5-5ef3eaa5c0f2
-- title:
--   Macaulay's pseudo-power a ↦ a^{⟨ d⟩} is strictly increasing
-- statement:
--   Fix a natural number $d$ with $1 \le d$, and natural numbers $a, b$ with $a < b$. The conclusion is $\mathrm{macaulayPow}\;d\;a < \mathrm{macaulayPow}\;d\;b$, where [`Nat.macaulayPow`](def/Nat_MacaulayPow.html#L7) is the greedy binomial expansion operator defined by recursion on its first argument: $\mathrm{macaulayPow}\;0\;a = 0$ for every $a$, and for $d+1$ one takes $k = k(d,a)$ to be the largest $k \le a + d + 1$ with $\binom{k}{d+1} \le a$ (computed by `Nat.findGreatest` over that search range) and sets
--   $$\mathrm{macaulayPow}\;(d+1)\;a = \binom{k+1}{d+2} + \mathrm{macaulayPow}\;d\;\bigl(a - \binom{k}{d+1}\bigr).$$
--   Thus for $d \ge 1$ the function $a \mapsto a^{\langle d\rangle}$ obtained by writing $a$ in its greedy (Macaulay) representation in binomials with lower indices $d, d-1, \dots$ and raising each top entry and each lower index by one is strictly monotone in $a$. Note that the hypothesis $1 \le d$ is needed, since [`Nat.macaulayPow 0`](def/Nat_MacaulayPow.html#L7) is identically $0$.
--
--   This is the strict monotonicity of Macaulay's upper pseudo-power, the arithmetic function controlling the Macaulay–Gotzmann bounds on Hilbert functions of graded quotients. It is used in the estimates for the ranks of graded pieces of polynomial rings modulo a linear form, in [`MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt`](thm.html#MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt) and [`MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`](thm.html#MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Nat_macaulayPow_lt_macaulayPow_of_lt.lean

import Mathlib
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Nat.macaulayPow_lt_macaulayPow_of_lt {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    Nat.macaulayPow d a < Nat.macaulayPow d b := by sorry
