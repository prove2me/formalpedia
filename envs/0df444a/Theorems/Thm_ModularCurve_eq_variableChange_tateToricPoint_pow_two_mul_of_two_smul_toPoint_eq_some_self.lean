-- Prove2me | Theorems.Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some_self
-- name    : ModularCurve.eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/e96e4526-91dd-5efb-9022-0aa6aa96847f
-- title:
--   Doubling the toric point U^q on a transformed Tate curve
-- statement:
--   Let $L$ be a field of characteristic $0$, let $q,\ell$ be nonzero natural numbers with $2 \le q$ and $3 \le \ell$, and let $U \in L^\times$ be a primitive $(\ell q)$-th root of unity. Let $Cy$ be a Weierstrass variable change over the Laurent series ring $\mathrm{LaurentSeries}\,L$, and let $W_2$ be a Weierstrass curve over that ring which is elliptic and satisfies $W_2 = Cy \cdot (\mathtt{tateBase}\,L\,q)$, where `tateBase L q` is the Tate curve over $\mathrm{LaurentSeries}\,L$ obtained from the universal Tate equation by the ring homomorphism `qExpand L q` that multiplies all exponents by $q$. Let $E_2$ be a quadruple $(x_P,y_P,x_Q,y_Q)$ of Laurent series equal to the $Cy$-transform of the quadruple both of whose slots are the toric point $\mathtt{tateToricPoint}\,L\,q\,(U^q)$ — the explicit pair of power series with coefficients given by the divisor sums in the definition of `tateToricPoint` with parameter $c = U^q$ and divisibility by $q$; thus $x_P = u^{-2}(x_T - r)$, $y_P = u^{-3}(y_T - s(x_T - r) - t)$ for $Cy = (u,r,s,t)$ and $(x_T,y_T) = \mathtt{tateToricPoint}\,L\,q\,(U^q)$. Assume $(x_P,y_P)$ is a nonsingular point of the affine curve attached to $W_2$, and let $X_2,Y_2$ be Laurent series with $(X_2,Y_2)$ nonsingular on that affine curve. If $2 \cdot \mathtt{toPoint}\,W_2\,x_P\,y_P$ (the affine point $(x_P,y_P)$ when nonsingular, and $0$ otherwise) equals the affine point $(X_2,Y_2)$ in the group of $W_2$, then $X_2$ and $Y_2$ are the first two entries of the $Cy$-transform of the quadruple both of whose slots are $\mathtt{tateToricPoint}\,L\,q\,(U^{2q})$; that is, $X_2 = u^{-2}(x_T' - r)$ and $Y_2 = u^{-3}(y_T' - s(x_T' - r) - t)$ with $(x_T',y_T') = \mathtt{tateToricPoint}\,L\,q\,(U^{2q})$.
--
--   This is the duplication formula for toric points on the Tate curve in its cuspidal $q$-expansion form: doubling the point with toric parameter $U^q$ produces the point with parameter $U^{2q}$, compatibly with a Weierstrass variable change, the hypothesis $3 \le \ell$ ensuring that the doubled index $(2q,0)$ remains nonzero modulo $\ell q$. It feeds the construction of level automorphisms at a cusp in the full-level analysis, where the second slot of the level data is taken to coincide with the first.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some_self.lean

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

theorem ModularCurve.eq_variableChange_tateToricPoint_pow_two_mul_of_two_smul_toPoint_eq_some_self
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ] (h2q : 2 ≤ q) (h3ℓ : 3 ≤ ℓ)
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (E₂ : ModularCurve.LevelPData (LaurentSeries L))
    (hE₂ : E₂ = (⟨(ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2,
        (ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy)
    (hP : W₂.toAffine.Nonsingular E₂.xP E₂.yP)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : (2 : ℤ) • ModularCurve.LevelRelabelling.toPoint W₂ E₂.xP E₂.yP = WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY) :
    X₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2,
        (ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).xP ∧
    Y₂ = ((⟨(ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2,
        (ModularCurve.tateToricPoint L q (U ^ (2 * q))).1, (ModularCurve.tateToricPoint L q (U ^ (2 * q))).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).yP := by sorry
