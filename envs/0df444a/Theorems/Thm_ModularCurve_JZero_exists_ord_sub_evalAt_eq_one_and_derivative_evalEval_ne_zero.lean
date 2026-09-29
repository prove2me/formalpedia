-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
-- name    : ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/4ae3f443-465c-59e6-a02b-39d58e0f24f7
-- title:
--   Good chart datum at a prescribed place of X₀(N)
-- statement:
--   Fix $N\ge 1$ (with `NeZero N`) and let $F$ denote `modularFunctionFieldBar N`, the compositum over $\overline{\mathbb Q}$ inside $\overline{\mathbb Q}((q))$ of the coefficientwise image of the modular function field of level $N$. Let $s:\mathrm{Fin}\,r\to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space of the divisor `embDivisor N` $=$ `embDegree N` times the cusp at infinity. Let $Q$ be a place of $F$ over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ and a principal ideal ring), and let $i$ be an index with $\mathrm{ord}_Q(s_i)\le \mathrm{ord}_Q(s_j)$ for all $j$, where $\mathrm{ord}_Q$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation. Then there are elements $z$ and $u_0,\dots,u_r$ of $F$, bivariate polynomials $G_0,\dots,G_r\in\overline{\mathbb Q}[X][Y]$, and integer vectors $(c_l)$, $(c_{k,l})$ and an integer matrix $(M_{l,k})$ such that: $z=\sum_l c_l\,(s_l s_i^{-1})$; $u_k=\sum_l c_{k,l}\,(s_l s_i^{-1})$ for every $k$; $s_l s_i^{-1}=\sum_k M_{l,k}u_k$ for every $l$; each $G_k$ is irreducible; every coefficient of every $G_k$ is integral over $\mathbb Z$; $G_k(z,u_k)=0$ and $(\partial G_k/\partial Y)(z,u_k)\neq 0$ in $F$, the derivative being taken in the outer variable; $\mathrm{ord}_Q\bigl(z-z(Q)\bigr)=1$, where $z(Q)\in\overline{\mathbb Q}$ is the residue evaluation `Q.evalAt z`; and $(\partial G_k/\partial Y)\bigl(z(Q),u_k(Q)\bigr)\neq 0$ in $\overline{\mathbb Q}$ for every $k$.
--
--   This produces, at a prescribed place $Q$ of the function field of $X_0(N)$ over $\overline{\mathbb Q}$, a chart datum in the sense of elementary function-field geometry: a function $z$ which is a uniformiser at $Q$ in the form $z-z(Q)$, together with coordinates $u_k$ that are integral linear combinations of the ratios $s_l/s_i$ and recover those ratios integrally, each satisfying an irreducible plane relation with $z$ that is simple at $Q$ both in $F$ and after evaluation. It is the local input from which non-archimedean discs around $Q$ (Hensel–Newton branches for the $u_k$) are obtained, and it is used by [`ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero`](thm.html#ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero), which supplies such data simultaneously for a family of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
    (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (i : Fin r)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : ∀ j, Q.ord (s i) ≤ Q.ord (s j)) :
    ∃ (z : modularFunctionFieldBar N)
      (u : Fin (r + 1) → modularFunctionFieldBar N)
      (G : Fin (r + 1) → Polynomial (Polynomial (AlgebraicClosure ℚ)))
      (cz : Fin r → ℤ) (cu : Fin (r + 1) → Fin r → ℤ)
      (M : Fin r → Fin (r + 1) → ℤ),
      (z = ∑ l, (cz l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) ∧
      (∀ k, u k = ∑ l, (cu k l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) ∧
      (∀ l, s l * (s i)⁻¹ = ∑ k, (M l k : AlgebraicClosure ℚ) • u k) ∧
      (∀ k, Irreducible (G k)) ∧
      (∀ k n n', IsIntegral ℤ (((G k).coeff n).coeff n')) ∧
      (∀ k, ((G k).map (Polynomial.mapRingHom
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))).evalEval z (u k) = 0) ∧
      (∀ k, ((Polynomial.derivative (G k)).map (Polynomial.mapRingHom
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))).evalEval z (u k) ≠ 0) ∧
      Q.ord (z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt z)) = 1 ∧
      (∀ k, (Polynomial.derivative (G k)).evalEval (Q.evalAt z) (Q.evalAt (u k)) ≠ 0) := by sorry
