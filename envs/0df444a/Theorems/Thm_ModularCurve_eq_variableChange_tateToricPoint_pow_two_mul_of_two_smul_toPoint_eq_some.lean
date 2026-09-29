-- Prove2me | Theorems.Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some
-- name    : ModularCurve.eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/64e4f6db-4b0e-5da7-89af-5d7eb65ac342
-- title:
--   Doubling the toric point: 2R reads as U^{2q}
-- statement:
--   Let $L$ be a field of characteristic zero, let $q,\ell$ be nonzero natural numbers with $2\le q$ and $3\le\ell$, and let $U\in L^{\times}$ be a primitive $(\ell q)$-th root of unity. Work over the Laurent series field $\mathrm{LaurentSeries}\,L$, and write $x_T(c),y_T(c)$ for the two components of [`ModularCurve.tateToricPoint L q c`](def/ModularCurve_KatzLevelPCusps.html#L20), the explicit pair of Laurent series whose coefficients are the divisor sums in $c$ and $c^{-1}$ cut out by divisibility by $q$. Let $C_y$ be a Weierstrass variable change over $\mathrm{LaurentSeries}\,L$, and let $W_2$ be an elliptic Weierstrass curve with $W_2=C_y\cdot(\mathtt{tateBase}\,L\,q)$, the Tate curve with exponents scaled by $q$ via [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25). Let $E_2$ be the level-$p$ datum obtained by applying the variable change $C_y$ to the quadruple $\bigl(x_T(U^{q}),y_T(U^{q}),x_T(U^{\ell}),y_T(U^{\ell})\bigr)$, so that, with $C_y=(u,r,s,t)$, $E_2.xP=u^{-2}(x_T(U^q)-r)$ and $E_2.yP=u^{-3}(y_T(U^q)-s(x_T(U^q)-r)-t)$, and similarly in the $Q$-slot. Assume $(E_2.xP,E_2.yP)$ and $(E_2.xQ,E_2.yQ)$ are nonsingular points of the affine model of $W_2$, let $X_2,Y_2$ be nonsingular affine coordinates on $W_2$, and assume that $2\cdot\mathtt{toPoint}\,W_2\,E_2.xP\,E_2.yP$ (the affine point $(E_2.xP,E_2.yP)$, taken to be $0$ when not nonsingular) equals the affine point $(X_2,Y_2)$. Then $X_2=u^{-2}(x_T(U^{2q})-r)$ and $Y_2=u^{-3}(y_T(U^{2q})-s(x_T(U^{2q})-r)-t)$, i.e. $(X_2,Y_2)$ is the $P$-slot of the $C_y$-transport of the quadruple built from $\mathtt{tateToricPoint}\,L\,q\,(U^{2q})$ and $\mathtt{tateToricPoint}\,L\,q\,(U^{\ell})$.
--
--   This is the duplication step in the cuspidal computation of level-$p$ data on Tate curves: doubling the first marked point of a toric cusp datum shifts its toric parameter from $U^{q}$ to $U^{2q}$, compatibly with an arbitrary Weierstrass variable change, the hypothesis $3\le\ell$ guaranteeing that the doubled index is still nonzero. It feeds the full-level auxiliary analysis of level automorphisms acting on toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some.lean

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

theorem ModularCurve.eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ] (h2q : 2 ≤ q) (h3ℓ : 3 ≤ ℓ)
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (E₂ : ModularCurve.LevelPData (LaurentSeries L))
    (hE₂ : E₂ = (⟨(ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy)
    (hP : W₂.toAffine.Nonsingular E₂.xP E₂.yP) (hQ : W₂.toAffine.Nonsingular E₂.xQ E₂.yQ)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : (2 : ℤ) • ModularCurve.LevelRelabelling.toPoint W₂ E₂.xP E₂.yP = WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY) :
    X₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).xP ∧
    Y₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2,
        (ModularCurve.tateToricPoint L q (U ^ ℓ)).1, (ModularCurve.tateToricPoint L q (U ^ ℓ)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).yP := by sorry
