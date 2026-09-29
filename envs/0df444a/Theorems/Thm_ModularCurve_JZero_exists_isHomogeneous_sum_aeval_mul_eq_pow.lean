-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow
-- name    : ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/16d36313-2421-565a-80cc-211fdff57f4f
-- title:
--   Homogeneous certificate s_k^{M+1}=sumⱼ qⱼ(s)uⱼ on X₀(N)
-- statement:
--   Fix $N\ge 1$ and work with the field $F=$ [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the subfield of $\overline{\mathbb Q}$-Laurent series obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise image of the modular function field of level $N$, regarded as a function field over $K=\overline{\mathbb Q}$ (an algebraic closure of $\mathbb Q$). Let $a,b\in\mathbb N$, let $s:\mathrm{Fin}\,a\to F$ and $u:\mathrm{Fin}\,b\to F$ be finite families with every $u_j\neq 0$, and let $D$ be a divisor, i.e. a finitely supported $\mathbb Z$-valued function on the places of $F/K$. Assume: the degree $\sum_v D(v)\deg v$ of $D$ is at least $2g+1$, where $g$ is the function-field genus `genusFF`; the $K$-span of the range of $s$ equals the Riemann–Roch space $L(D)=\{f: v(f)\le \exp(D v)\ \text{for all places } v\}$; each $u_j$ lies in $L(D)$; and for every place $w$ there is some $j$ with $\operatorname{ord}_w(u_j)+D(w)=0$, i.e. the family $u$ is base-point free for $D$. Then there exists $M\in\mathbb N$ such that for every index $k<a$ one can find polynomials $q_j\in K[X_0,\dots,X_{a-1}]$, $j<b$, each homogeneous of degree $M$, with $\sum_{j} q_j(s_0,\dots,s_{a-1})\,u_j=s_k^{\,M+1}$ in $F$.
--
--   This is the algebraic half of Weil's height machine for the pair consisting of the complete linear system $L(D)$ on $X_0(N)$ and the base-point-free subsystem spanned by the $u_j$: a projective Nullstellensatz certificate expressing that the linear projection onto the $u$-coordinates has no centre on the curve. It is used in the comparison of the heights attached to the two systems, [`ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero`](thm.html#ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(ModularCurve.modularFunctionFieldBar N)) (u : Fin b → ↥(ModularCurve.modularFunctionFieldBar N))
    (hu : ∀ j, u j ≠ 0)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hd : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D)
    (huD : ∀ j, u j ∈ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ∃ j, w.ord (u j) + D w = 0) :
    ∃ M : ℕ, ∀ k : Fin a, ∃ q : Fin b → MvPolynomial (Fin a) (AlgebraicClosure ℚ),
      (∀ j, (q j).IsHomogeneous M) ∧
      ∑ j, MvPolynomial.aeval s (q j) * u j = s k ^ (M + 1) := by sorry
