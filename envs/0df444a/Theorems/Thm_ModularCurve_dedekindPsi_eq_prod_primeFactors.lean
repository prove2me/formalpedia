-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_eq_prod_primeFactors
-- name    : ModularCurve.dedekindPsi_eq_prod_primeFactors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/5b2f8b8a-9f8c-5adb-ad1b-9be3e685c704
-- title:
--   Closed product formula for ψ(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. The function `dedekindPsi` is defined on natural numbers by $\psi(N) = \sum_{d} N/d$, the sum running over those divisors $d$ of $N$ that are squarefree, with $N/d$ the natural-number quotient. The assertion is the identity, in $\mathbb{N}$, $$\psi(N) = \prod_{p \in \mathrm{primeFactors}(N)} p^{v_p(N)-1}\,(p+1),$$ where the product is over the finite set of prime divisors of $N$ and $v_p(N)$ denotes the exponent of $p$ in the factorisation of $N$. The subtraction in the exponent is natural-number truncated subtraction, which is harmless since $v_p(N) \geq 1$ for every $p$ dividing $N$. Thus the classical closed form $N \prod_{p \mid N} (1 + 1/p)$ of the Dedekind psi function is expressed entirely within $\mathbb{N}$, without dividing in $\mathbb{Q}$.
--
--   This is the closed product form of the Dedekind psi function, the quantity $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]$, equal to the degree of $X_0(N) \to X(1)$. It is used to match $\psi(N)$ against explicit integer formulas, in computations of ranks of function-field constructions attached to modular curves and in a count of $\Gamma_0$-power tuples over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_eq_prod_primeFactors.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.dedekindPsi_eq_prod_primeFactors (N : ℕ) (hN : N ≠ 0) :
    dedekindPsi N = ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1) := by sorry
