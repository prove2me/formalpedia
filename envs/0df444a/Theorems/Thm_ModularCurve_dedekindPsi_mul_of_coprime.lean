-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
-- name    : ModularCurve.dedekindPsi_mul_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/279a2b31-54aa-5736-b408-0c9a53ca3d30
-- title:
--   Multiplicativity of the Dedekind ψ function
-- statement:
--   For natural numbers $M$ and $N$ that are coprime, the function $\psi$ defined by $$\psi(N) = \sum_{\substack{d \mid N \\ d \text{ squarefree}}} N/d,$$ the sum being over the divisors $d$ of $N$ in the sense of `Nat.divisors` (so over an empty set when $N = 0$) that are squarefree, with $N/d$ the quotient of natural numbers, which is exact since $d$ divides $N$, satisfies $\psi(MN) = \psi(M)\,\psi(N)$. No positivity hypothesis is imposed on $M$ or $N$: the case where one of them vanishes is covered, both sides then being $0$ unless the other is $1$. Thus `dedekindPsi` is multiplicative on coprime pairs; for $N \geq 1$ its value is $N \prod_{p \mid N} (1 + 1/p)$, but that closed form is not what the statement asserts.
--
--   This is the multiplicativity, on coprime arguments, of the Dedekind $\psi$ function, which computes the index of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$. It is used throughout the index and genus computations for the modular curves $X_0(N)$ and their relatives, for instance in reducing such quantities to prime powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) : dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by sorry
