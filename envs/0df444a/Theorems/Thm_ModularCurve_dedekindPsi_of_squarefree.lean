-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_of_squarefree
-- name    : ModularCurve.dedekindPsi_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/7d026fe4-23a4-5b1a-9f86-5ecdcf6436bc
-- title:
--   Dedekind ψ at squarefree level
-- statement:
--   Let $N$ be a natural number which is squarefree. Here $\psi(N)$ is defined as the natural-number sum $\sum_{d} N/d$, taken over those $d$ in the finset of divisors of $N$ which are themselves squarefree, the quotient being natural division (for $N = 0$ the divisor finset is empty, so $\psi(0) = 0$; squarefreeness of $N$ in any case forces $N \neq 0$). The assertion is the equality of natural numbers $$\psi(N) = \prod_{p \in \mathrm{primeFactors}(N)} (p + 1),$$ the product running over the finset of prime factors of $N$. In particular the right-hand side is the empty product $1$ when $N = 1$, matching $\psi(1) = 1$. Thus for squarefree $N$ the sum over squarefree divisors collapses to the familiar product formula $N \prod_{p \mid N} (1 + 1/p)$, stated here in the integral form $\prod_{p \mid N}(p+1)$.
--
--   The function $\psi$ is Dedekind's psi function, the degree of the modular equation of level $N$, i.e. the expected degree of the function field of $X_0(N)$ over $\mathbb{Q}(j)$. This closed formula at squarefree levels is used by the statements on the degree of $\mathbb{Q}(j)(j_N)$ over $\mathbb{Q}(j)$ and on generation of the function field at squarefree level, such as [`ModularCurve.finrank_adjoin_jqN_eq_of_squarefree`](thm.html#ModularCurve.finrank_adjoin_jqN_eq_of_squarefree), [`ModularCurve.functionFieldGeneration_of_squarefree`](thm.html#ModularCurve.functionFieldGeneration_of_squarefree) and [`ModularCurve.relfinrank_adjoin_primes`](thm.html#ModularCurve.relfinrank_adjoin_primes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_of_squarefree.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.dedekindPsi_of_squarefree {N : ℕ} (hN : Squarefree N) : dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) := by sorry
