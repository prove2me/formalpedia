-- Prove2me | Theorems.Thm_ModularCurve_eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
-- name    : ModularCurve.eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/999fd2b3-f1df-55ee-b1dd-1cc2dbd1817b
-- title:
--   Toric plus non-toric Tate point sums to a non-toric point
-- statement:
--   Let $L$ be a field of characteristic zero, let $q,\ell$ be nonzero naturals with $2\le q$ and $2\le\ell$, let $j$ satisfy $0<j<q$, and let $U\in L^{\times}$ be a primitive $(\ell q)$-th root of unity. Work over the Laurent series field `LaurentSeries L`, let `Cy` be a Weierstrass variable change $(u,r,s,t)$ over it, and let $W_2$ be an elliptic Weierstrass curve with $W_2 =$ `Cy` $\bullet$ `tateBase L q`, the Tate curve `tateLaurent L` pushed along the substitution `qExpand L q` that multiplies Hahn exponents by $q$. Let $E_2$ be the level-$P$ datum (a quadruple $x_P,y_P,x_Q,y_Q$) obtained by applying `Cy` coordinatewise — $x\mapsto u^{-2}(x-r)$, $y\mapsto u^{-3}(y-s(x-r)-t)$ — to the quadruple whose $P$-part is `tateToricPoint L q (U ^ q)`, the explicit pair of Laurent series with constant terms $c\,(1-c)^{-2}$ and $c^{2}(1-c)^{-3}$ for $c=U^{q}$ and higher coefficients given by the divisor sums of the Tate parametrisation at level $q$, and whose $Q$-part is `nonToricPoint L q 1 j`, the pair obtained by substituting the slot family `slotFamily L q 1 j` into the universal series `tateUnivX`, `tateUnivY`. Assume both coordinate pairs of $E_2$ are nonsingular on the affine model of $W_2$, and let $X_2,Y_2$ be a nonsingular pair such that the sum of the two corresponding affine points of $W_2$ (each taken via `toPoint`, which returns the point if nonsingular and $0$ otherwise) equals the affine point $(X_2,Y_2)$. Then $(X_2,Y_2)$ is the $P$-coordinate pair of the `Cy`-transport of the quadruple with $P$-part `nonToricPoint L q (U ^ q) j` and $Q$-part `nonToricPoint L q 1 j`.
--
--   This is one of the cusp-side computations for the Tate curve: the sum of the toric point with parameter $U^{q}$ and the non-toric point at slot $(1,j)$ on the $q$-fold Tate curve is again a non-toric point, with parameter $U^{q}$ at the same slot, and the identity is stated in coordinates transported by an arbitrary variable change. It is used in the construction of level structures and their automorphisms at the cusps, being cited in the verification that a suitable level automorphism carries prescribed toric and non-toric points to each other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some.lean

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

theorem ModularCurve.eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ] (h2q : 2 ≤ q) (h2ℓ : 2 ≤ ℓ) (j : ℕ) (hj : 0 < j) (hjq : j < q)
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (E₂ : ModularCurve.LevelPData (LaurentSeries L))
    (hE₂ : E₂ = (⟨(ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy)
    (hP : W₂.toAffine.Nonsingular E₂.xP E₂.yP) (hQ : W₂.toAffine.Nonsingular E₂.xQ E₂.yQ)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : ModularCurve.LevelRelabelling.toPoint W₂ E₂.xP E₂.yP + ModularCurve.LevelRelabelling.toPoint W₂ E₂.xQ E₂.yQ =
      WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY) :
    X₂ = ((⟨(ModularCurve.nonToricPoint L q (U ^ q) j).1, (ModularCurve.nonToricPoint L q (U ^ q) j).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).xP ∧
    Y₂ = ((⟨(ModularCurve.nonToricPoint L q (U ^ q) j).1, (ModularCurve.nonToricPoint L q (U ^ q) j).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).yP := by sorry
