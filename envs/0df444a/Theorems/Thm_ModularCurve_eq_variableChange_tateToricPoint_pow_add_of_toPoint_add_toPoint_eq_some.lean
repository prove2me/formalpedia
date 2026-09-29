-- Prove2me | Theorems.Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_add_of_toPoint_add_toPoint_eq_some
-- name    : ModularCurve.eq_variableChange_tateToricPoint_pow_add_of_toPoint_add_toPoint_eq_some
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/39c492c9-08ac-5dda-98d0-2812011a0d05
-- title:
--   Toric points on the Tate curve add: U^q+U^ℓ=U^{q+ℓ}
-- statement:
--   Let $L$ be a field of characteristic zero, let $q,\ell$ be nonzero natural numbers with $2\le q$, $2\le\ell$ and $q+\ell<\ell q$, and let $U\in L^{\times}$ be a primitive $(\ell q)$-th root of unity. Work over the Laurent series field $L((\mathsf q))$. Write $x_T(c),y_T(c)$ for the two components of [`ModularCurve.tateToricPoint L q c`](def/ModularCurve_KatzLevelPCusps.html#L20), the explicit Laurent series attached to a unit $c$, whose coefficient at $m>0$ is the divisor sum $\sum_{d\mid m,\;q\mid d}(m/d)\bigl(c^{m/d}+c^{-(m/d)}\bigr)-2[q\mid m]\sigma_1(m/q)$ for the first component and the corresponding binomial-weighted sum $\sum_{d\mid m,\;q\mid d}\bigl(\binom{m/d}{2}c^{m/d}-\binom{m/d+1}{2}c^{-(m/d)}\bigr)+[q\mid m]\sigma_1(m/q)$ for the second, with constant terms $c/(1-c)^2$ and $c^2/(1-c)^3$. Let $C_y=(u,r,s,t)$ be a Weierstrass variable change over $L((\mathsf q))$ and let $W_2$ be an elliptic Weierstrass curve with $W_2=C_y\cdot\,$[`ModularCurve.tateBase L q`](def/ModularCurve_TateSlots.html#L46), the Tate curve over $L((\mathsf q))$ pushed forward along $\mathsf q\mapsto\mathsf q^{q}$. Let $E_2$ be the level-$p$ datum obtained by applying $C_y$ to the quadruple with $P$-slot $(x_T(U^q),y_T(U^q))$ and $Q$-slot $(x_T(U^{\ell}),y_T(U^{\ell}))$, so that its entries are $u^{-2}(x-r)$ and $u^{-3}(y-s(x-r)-t)$ in each slot. Assume both slots of $E_2$ are nonsingular points of the affine model of $W_2$, and let $X_2,Y_2$ be Laurent series with $(X_2,Y_2)$ nonsingular on $W_2$ such that, in the group of affine points of $W_2$, the sum of the points determined by the $P$- and $Q$-slots of $E_2$ (each taken to be the corresponding affine point, since it is nonsingular) equals the affine point $(X_2,Y_2)$. The conclusion is that $X_2$ and $Y_2$ are the $P$-slot coordinates of the $C_y$-transport of the quadruple with $P$-slot $(x_T(U^{q+\ell}),y_T(U^{q+\ell}))$ and $Q$-slot $(x_T(U^{\ell}),y_T(U^{\ell}))$, that is $X_2=u^{-2}\bigl(x_T(U^{q+\ell})-r\bigr)$ and $Y_2=u^{-3}\bigl(y_T(U^{q+\ell})-s(x_T(U^{q+\ell})-r)-t\bigr)$.
--
--   This is the Tate-curve (cuspidal) reading of one point addition on a level structure: adding the toric points with parameters $U^q$ and $U^{\ell}$ on the Tate curve with parameter $\mathsf q^{q}$ produces the toric point with parameter $U^{q+\ell}$, and the identification persists after an arbitrary Weierstrass change of variables $C_y$. It feeds the computation of level structures at the cusps used in [`ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_tateToricPoint_sub_and_apply_eq_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_tateToricPoint_sub_and_apply_eq_of_isPrimitiveRoot_mul_of_dvd), the proof proceeding by raising the level along $\mathsf q\mapsto\mathsf q^{\ell}$, where the toric points become cusp points whose indices add.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_add_of_toPoint_add_toPoint_eq_some.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Classical

theorem ModularCurve.eq_variableChange_tateToricPoint_pow_add_of_toPoint_add_toPoint_eq_some
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ] (h2q : 2 ≤ q) (h2ℓ : 2 ≤ ℓ) (hqℓ : q + ℓ < ℓ * q)
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (E₂ : ModularCurve.LevelPData (LaurentSeries L))
    (hE₂ : E₂ = (⟨(ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy)
    (hP : W₂.toAffine.Nonsingular E₂.xP E₂.yP) (hQ : W₂.toAffine.Nonsingular E₂.xQ E₂.yQ)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : ModularCurve.LevelRelabelling.toPoint W₂ E₂.xP E₂.yP + ModularCurve.LevelRelabelling.toPoint W₂ E₂.xQ E₂.yQ =
      WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY) :
    X₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (q + ℓ))).1, (ModularCurve.tateToricPoint L q (U ^ (q + ℓ))).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).xP ∧
    Y₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (q + ℓ))).1, (ModularCurve.tateToricPoint L q (U ^ (q + ℓ))).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).yP := by sorry
