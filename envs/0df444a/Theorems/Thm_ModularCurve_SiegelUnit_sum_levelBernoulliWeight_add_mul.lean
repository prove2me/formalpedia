-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul
-- name    : ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/c318ba77-3fc3-5445-aefa-2fdb70d5c91d
-- title:
--   Distribution relation for the quadratic Bernoulli weight 6t²-6Nt+N²
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $p, r$ be arbitrary integers. For $s \in \mathbb{Z}/N\mathbb{Z}$ write $t(s) \in \{0,1,\dots,N-1\}$ for the canonical representative (`ZMod.val`) of the residue class $\bar p + s\,\bar r \in \mathbb{Z}/N\mathbb{Z}$, where $\bar p, \bar r$ are the reductions of $p$ and $r$, and regard $t(s)$ as an integer. Let $g = \gcd(r, N)$ be the integer greatest common divisor (`Int.gcd`, a natural number, so $g = N$ when $N \mid r$, and $g \geq 1$ since $N \neq 0$), and let $p \bmod g$ denote the integer remainder (`Int.emod`), which lies in $\{0,1,\dots,g-1\}$. The assertion is the identity in $\mathbb{Z}$
--   $$\sum_{s \in \mathbb{Z}/N\mathbb{Z}} \bigl(6\,t(s)^2 - 6N\,t(s) + N^2\bigr) \;=\; N\bigl(6\,(p \bmod g)^2 - 6g\,(p \bmod g) + g^2\bigr),$$
--   the sum being over all $N$ elements of $\mathbb{Z}/N\mathbb{Z}$. Thus summing the level-$N$ weight $6t^2 - 6Nt + N^2$ over the arithmetic progression $p + s r$ modulo $N$ yields $N$ times the corresponding level-$g$ weight evaluated at the least non-negative residue of $p$ modulo $g$.
--
--   The integer $6t^2 - 6Nt + N^2 = 6N^2\,\overline{B}_2(t/N)$ is the standard bookkeeping weight for orders of Siegel functions at the cusps, and the identity is the distribution (Raabe multiplication) relation for the periodic second Bernoulli function, written so that both sides are integers. It is used in the construction of Siegel units, where it feeds [`ModularCurve.SiegelUnit.exists_peaked_exponent`](thm.html#ModularCurve.SiegelUnit.exists_peaked_exponent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N,
        (6 * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) + (N : ℤ) ^ 2) =
      (N : ℤ) * (6 * (p % (Int.gcd r N : ℤ)) ^ 2
        - 6 * (Int.gcd r N : ℤ) * (p % (Int.gcd r N : ℤ)) + (Int.gcd r N : ℤ) ^ 2) := by sorry
