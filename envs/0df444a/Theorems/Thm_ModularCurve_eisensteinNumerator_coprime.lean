-- Prove2me | Theorems.Thm_ModularCurve_eisensteinNumerator_coprime
-- name    : ModularCurve.eisensteinNumerator_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/9acd128d-7830-5cc5-a76d-f2be8756a593
-- title:
--   The Eisenstein numerator is coprime to p
-- statement:
--   Let $p$ be a natural number with $p \neq 0$. The Eisenstein numerator of $p$ is the natural number $\operatorname{eisensteinNumerator} p = (p-1)/\gcd(p-1,12)$, formed with truncated subtraction and natural division; since $\gcd(p-1,12)$ divides $p-1$, this is an exact quotient, namely the numerator of the fraction $(p-1)/12$ in lowest terms. The assertion is that $\operatorname{eisensteinNumerator} p$ and $p$ are coprime, i.e. $\gcd\bigl((p-1)/\gcd(p-1,12),\,p\bigr) = 1$. No primality or size hypothesis on $p$ is imposed; only $p \neq 0$ is required, this being needed because for $p = 0$ truncated subtraction gives $0 - 1 = 0$ and the numerator is $0$, which is not coprime to $0$.
--
--   For a prime $p \ge 5$ the quantity $(p-1)/\gcd(p-1,12)$ is the order of the component group of the Néron model of $J_0(p)$ at $p$, of the cuspidal divisor class $(0)-(\infty)$, and of the Shimura subgroup; this lemma records that this order is prime to the residue characteristic, the form in which the fact is used in arguments with Néron models and with $p$-power torsion. It is cited in the computations of the component group and of the $j$-invariant-zero torsion in the modular curve development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinNumerator_coprime.lean

import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem eisensteinNumerator_coprime (p : ℕ) (hp : p ≠ 0) : (eisensteinNumerator p).Coprime p := by sorry
