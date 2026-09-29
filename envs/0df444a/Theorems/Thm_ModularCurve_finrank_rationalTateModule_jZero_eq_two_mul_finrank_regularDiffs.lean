-- Prove2me | Theorems.Thm_ModularCurve_finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs
-- name    : ModularCurve.finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/c8cdaef4-d0f5-5a6b-8b08-ce7bf95461ad
-- title:
--   Rational p-adic Tate module of J₀(N) has dimension 2g
-- statement:
--   Fix a natural number $N$ assumed nonzero and a natural number $p$ assumed prime. Write $\bar{\mathbb{Q}}$ for `AlgebraicClosure ℚ` and let $F_N$ be `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\bar{\mathbb{Q}}((t))$ obtained by adjoining to $\bar{\mathbb{Q}}$ the coefficientwise images of the elements of `modularFunctionFieldFull N`, the latter being the subfield of $\mathbb{Q}((t))$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$. Let `JZero N` be $\mathrm{Pic}^0$ of $F_N$ over $\bar{\mathbb{Q}}$, i.e. the quotient of the group of degree-zero divisors by the subgroup of principal divisors. The theorem asserts an equality of two natural numbers. On the left is the $\mathbb{Q}_p$-dimension of $\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p$, where $T_p$ is the group of sequences $(x_n)_{n \in \mathbb{N}}$ in `JZero N` satisfying $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ for all $n$. On the right is twice the $\bar{\mathbb{Q}}$-dimension of `regularDiffs`, the $\bar{\mathbb{Q}}$-span inside $\Omega[F_N/\bar{\mathbb{Q}}]$ of those differentials $\omega$ with $0 \le v.\mathrm{ordDiff}\,\omega$ at every place $v$ of $F_N$ over $\bar{\mathbb{Q}}$.
--
--   This is the matching of étale and Hodge dimensions for the modular Jacobian: the rational $p$-adic Tate module of $J_0(N)$ has dimension $2g$, where $g$ is the dimension of the space of regular differentials on the modular curve, uniformly in $p$ (including primes dividing $N$). It feeds the torsion statement [`ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero`](thm.html#ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero), and underlies trace comparisons between the two spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs.lean

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] (RationalTateModule p (JZero N))
      = 2 * Module.finrank (AlgebraicClosure ℚ)
          ↥(AlgebraicCurve.regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := by sorry
