-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_prime
-- name    : ModularCurve.dedekindPsi_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/78858587-fcf2-5ab7-b77b-f7327132f734
-- title:
--   Value of `dedekindPsi` at a prime: ψ(p)=p+1
-- statement:
--   Let $p$ be a natural number, and assume $p$ is prime. The quantity $\mathrm{dedekindPsi}\,N$ is defined, for a natural number $N$, as the sum $\sum_{d} N/d$ taken over those divisors $d$ of $N$ (in the sense of `Nat.divisors`, so positive divisors of a nonzero $N$) that are squarefree, the quotient $N/d$ being natural-number division. The theorem asserts the equality of natural numbers $\mathrm{dedekindPsi}\,p = p + 1$. Since the divisors of a prime $p$ are exactly $1$ and $p$, and both are squarefree, the defining sum has precisely the two terms $p/1 = p$ and $p/p = 1$. Thus the statement is the evaluation at a prime of the arithmetic function whose general value is $\psi(N) = N\prod_{\ell \mid N}(1 + 1/\ell)$, here presented through its squarefree-divisor sum definition; no further hypotheses beyond primality of $p$ enter.
--
--   The function $\mathrm{dedekindPsi}$ is the Dedekind $\psi$ function, which for level $N$ records the index $[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(N)]$ and the degree in each variable of the modular polynomial $\Phi_N$; the present lemma is the prime case $\psi(p)=p+1$. It is used throughout the algebraic treatment of $X_0(N)$ in the project, for instance in the counting arguments for fibres over the $j$-line and in the genus and cusp estimates that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_prime.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by sorry
