-- Prove2me | Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
-- name    : Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/b06d4b30-422a-5741-8b6b-7cf28d12a088
-- title:
--   Eventual equality in Macaulay's growth bound
-- statement:
--   Let $H : \mathbb{N} \to \mathbb{N}$ be an arbitrary function of natural numbers and let $d_0 \geq 1$ be a natural number. Here $\mathtt{Nat.macaulayPow}\ d\ a$ is defined by recursion on the first argument: it is $0$ for $d = 0$, and for $d+1$ it is $\binom{k+1}{d+2} + \mathtt{Nat.macaulayPow}\ d\ (a - \binom{k}{d+1})$, where $k$ is the greatest natural number $\le a+d+1$ with $\binom{k}{d+1} \le a$ (and $k = 0$ if there is none); this is Macaulay's upper pseudo-power $a^{\langle d\rangle}$, obtained by raising each entry of the $d$-th Macaulay representation of $a$ one step. Assume that for every $d$ with $d_0 \le d$ one has the growth bound $H(d+1) \le \mathtt{Nat.macaulayPow}\ d\ (H(d))$. The conclusion is that there exists a natural number $D_0$ such that for every $e$ with $D_0 \le e$ the bound is an equality, $H(e+1) = \mathtt{Nat.macaulayPow}\ e\ (H(e))$; no relation between $D_0$ and $d_0$, and no bound on $D_0$ in terms of $H$, is asserted.
--
--   This is the combinatorial core of Gotzmann's persistence phenomenon: a numerical function satisfying Macaulay's growth bound from some degree on must eventually grow maximally, which is what produces a Gotzmann number. It is used in the treatment of Hilbert functions of graded quotients and of the Hilbert functor, for instance in establishing that the relevant Hilbert functions eventually agree with a polynomial and in the associated finiteness statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.lean

import Mathlib
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
    (H : ℕ → ℕ) (d₀ : ℕ) (hd₀ : 1 ≤ d₀)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) := by sorry
