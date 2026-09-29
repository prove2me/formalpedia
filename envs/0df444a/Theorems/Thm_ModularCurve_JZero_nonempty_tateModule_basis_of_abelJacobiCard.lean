-- Prove2me | Theorems.Thm_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard
-- name    : ModularCurve.JZero.nonempty_tateModule_basis_of_abelJacobiCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/935a557f-9fe4-5e15-923e-7f74def4c1fa
-- title:
--   Tate module of J₀(N) free of rank 2g
-- statement:
--   Let $N$, $p$, $g$ be natural numbers with $p$ prime. Write $K=\overline{\mathbb{Q}}$ for the algebraic closure of $\mathbb{Q}$ and let $F$ be [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the subfield of the Laurent series field $\overline{\mathbb{Q}}((t))$ generated over $\overline{\mathbb{Q}}$ by the image, under coefficientwise inclusion, of the modular function field of level $N$ (itself the subfield of $\mathbb{Q}((t))$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$). Let $J_0(N)$ denote [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisors of $F/K$ modulo principal divisors. The hypothesis is [`AlgebraicCurve.AbelJacobiCard K F p g`](def/AlgebraicCurve_DivisorClassGroup.html#L252): for every $n$ the subgroup of elements of $J_0(N)$ killed by $p^n$ has exactly $p^{2gn}$ elements. Under this hypothesis, the $p$-adic Tate module of $J_0(N)$ — the group of sequences $(x_n)_{n\in\mathbb{N}}$ in $J_0(N)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$ for all $n$ — admits, as a $\mathbb{Z}_p$-module, a basis indexed by $\mathrm{Fin}(2g)$; that is, it is free of rank $2g$ over $\mathbb{Z}_p$. No relation between $g$ and the genus of the curve is assumed: $g$ enters only through the counting hypothesis.
--
--   This is the integral form of the classical statement that the $p$-adic Tate module of the Jacobian of a smooth projective curve of genus $g$ over an algebraically closed field of characteristic $0$ is free of rank $2g$ over $\mathbb{Z}_p$, here derived from the Abel–Jacobi torsion count alone. It is used by [`ModularCurve.finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs`](thm.html#ModularCurve.finrank_rationalTateModule_jZero_eq_two_mul_finrank_regularDiffs) to identify the dimension of the rational Tate module of $J_0(N)$ with twice the dimension of the space of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.JZero.nonempty_tateModule_basis_of_abelJacobiCard :
    ∀ (N p g : ℕ) (hp : p.Prime),
      haveI : Fact p.Prime := ⟨hp⟩
      AlgebraicCurve.AbelJacobiCard (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) p g →
        Nonempty (Module.Basis (Fin (2 * g)) ℤ_[p] (TateModule p (ModularCurve.JZero N))) := by sorry
