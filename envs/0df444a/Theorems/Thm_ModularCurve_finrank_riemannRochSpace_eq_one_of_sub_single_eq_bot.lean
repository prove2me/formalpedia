-- Prove2me | Theorems.Thm_ModularCurve_finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot
-- name    : ModularCurve.finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/5c9c6714-b39b-5466-abe9-8f2e72d126c9
-- title:
--   Effective divisor with L(D-v)=0 has ℓ(D)=1
-- statement:
--   Fix $N\ge 1$ and work with the field $\bar F_N$ obtained from the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$ (the function field `modularFunctionFieldFull N`) by base change along the coefficientwise embedding into $\overline{\mathbb{Q}}((q))$, i.e. $\bar F_N =$ `modularFunctionFieldBar N` is the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of that field. Here a place of $\bar F_N$ over $\overline{\mathbb{Q}}$ is a valuation subring containing the image of $\overline{\mathbb{Q}}$, distinct from the whole field and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $D$ be such a divisor with $D\ge 0$, i.e. $D(w)\ge 0$ for every place $w$, and let $v$ be a place of $\bar F_N$ over $\overline{\mathbb{Q}}$. Assume that the Riemann–Roch space of $D-\delta_v$, namely the $\overline{\mathbb{Q}}$-submodule of $f\in\bar F_N$ with $v_w(f)\le \exp\big((D-\delta_v)(w)\big)$ in the value group $\mathbb{Z}^{m0}$ for all places $w$, is the zero submodule. Then the Riemann–Roch space of $D$ has $\overline{\mathbb{Q}}$-dimension exactly $1$.
--
--   This is the standard consequence of the fact that imposing a zero at a rational point drops the dimension of a linear system by at most one: an effective divisor whose associated linear system becomes empty after subtracting a point has only the constants in its Riemann–Roch space. It is used in the analysis of divisors on $X_0(N)$ over $\overline{\mathbb{Q}}$, in particular by [`ModularCurve.JZero.exists_isRepOf_forall_apply_cuspInftyBar_le`](thm.html#ModularCurve.JZero.exists_isRepOf_forall_apply_cuspInftyBar_le) and by the computation of the dimension attached to a canonical divisor with the cusp removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot (N : ℕ) [NeZero N]
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hD : 0 ≤ D)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : riemannRochSpace (D - Finsupp.single v (1 : ℤ)) = ⊥) :
    Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) = 1 := by sorry
