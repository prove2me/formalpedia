-- Prove2me | Theorems.Thm_ModularCurve_nuTwo_prime
-- name    : ModularCurve.nuTwo_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/99e1a614-b898-53fe-83c9-7f1627891fb2
-- title:
--   Number of square roots of -1 in 𝔽ₚ
-- statement:
--   Let $p$ be a natural number which is prime and different from $2$. The quantity $\nu_2(p)$ is defined as the cardinality (as a natural number, via `Nat.card`) of the subtype of elements $x$ of $\mathbb{Z}/p\mathbb{Z}$ satisfying $x^2 + 1 = 0$, that is, the number of square roots of $-1$ in $\mathbb{Z}/p\mathbb{Z}$. The theorem asserts that this number equals $2$ if $p \bmod 4 = 1$, and $0$ otherwise. Since $p$ is an odd prime, the alternative case is $p \bmod 4 = 3$. Note that the statement is about the counting function $\nu_2$ of the definition module, namely the count of solutions of $x^2 = -1$ in $\mathbb{Z}/N\mathbb{Z}$ specialised to $N = p$; no modular curve or elliptic point enters the formal statement.
--
--   This is the first supplementary law of quadratic reciprocity, in the shape of the local factor $1 + \left(\frac{-1}{p}\right)$ occurring in the standard formula for the number of order-$2$ elliptic points of $\Gamma_0(N)$. It feeds the genus and cusp-count computations for modular curves of prime level used elsewhere in the development, for instance in the comparison of genus with the cardinality of certain level-one fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nuTwo_prime.lean

import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.nuTwo_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : nuTwo p = if p % 4 = 1 then 2 else 0 := by sorry
