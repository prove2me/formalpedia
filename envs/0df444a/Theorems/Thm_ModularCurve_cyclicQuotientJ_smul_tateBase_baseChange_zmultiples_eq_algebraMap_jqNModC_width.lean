-- Prove2me | Theorems.Thm_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
-- name    : ModularCurve.cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/f8a112aa-8202-54a7-b794-138c2943addc
-- title:
--   Quotient j-invariant of the width-w Tate curve
-- statement:
--   Let $F$ and $\Lambda$ be fields with $\Lambda$ an algebra over the Laurent series field $\mathrm{LaurentSeries}\,F$, and let $w,M'$ be nonzero naturals with $M'\neq 0$ in $F$ and $\zeta\in F$ a primitive $M'$-th root of unity. Write $E_w$ for [`ModularCurve.tateBase F w`](def/ModularCurve_TateSlots.html#L46), the universal Tate Weierstrass curve `tateLaurent F` pushed forward along the ring endomorphism `qExpand F w` of $\mathrm{LaurentSeries}\,F$ that multiplies Hahn-series exponents by $w$ (that is, $q\mapsto q^{w}$), and let $E_w^{\Lambda}$ be its base change to $\Lambda$. Let $C$ be a Weierstrass variable change over $\Lambda$ and $g$ a point of the affine curve $C\bullet E_w^{\Lambda}$ such that $n\cdot g=0$ exactly when $M'\mid n$, and such that for every $n$ with $M'\nmid n$ the transported point `vcFun C E_w^Λ (n • g)` is the affine point of $E_w^{\Lambda}$ whose coordinates are the images under $\mathrm{LaurentSeries}\,F\to\Lambda$ of the two explicit Laurent series [`ModularCurve.toricPoint F w (ζ ^ n)`](def/ModularCurve_TateSlots.html#L125). Let $d$ be a nonzero natural dividing $M'$. Then the quantity $c_4^3/\Delta$ of the curve `cyclicQuotientCurve` attached to $C\bullet E_w^{\Lambda}$, the subgroup of integer multiples of $(M'/d)\cdot g$, and the parameter $d$, equals the image in $\Lambda$ of [`ModularCurve.jqNModC F (w * d)`](def/ModularCurve_JqCoeff.html#L18), namely of $q^{-wd}$ times the integral $j$-numerator series in $q^{wd}$.
--
--   This identifies the $j$-invariant of the quotient of a twisted width-$w$ Tate curve by the order-$d$ part of its toric $M'$-torsion with $j(q^{wd})$, the classical computation that quotienting the Tate curve $E_q$ by $\mu_d$ yields $E_{q^{d}}$. It feeds the full-level Diamond-type argument, where the two instances $w=q\ell'$ and $w=q$ occur.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width.lean

import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
    (F : Type) [Field F] [DecidableEq F] (Λ : Type) [Field Λ] [DecidableEq Λ] [Algebra (LaurentSeries F) Λ]
    (w M' : ℕ) [NeZero w] [NeZero M'] (hM'F : ((M' : ℕ) : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M')
    (C : WeierstrassCurve.VariableChange Λ)
    (g : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point)
    (hg0 : ∀ n : ℕ, n • g = 0 ↔ M' ∣ n)
    (hg : ∀ n : ℕ, ¬ M' ∣ n →
        ∃ h₁ : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).1)
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).2),
          WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) (n • g) =
            WeierstrassCurve.Affine.Point.some _ _ h₁)
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    (C • (ModularCurve.tateBase F w).baseChange Λ).cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g)) d =
      algebraMap (LaurentSeries F) Λ (ModularCurve.jqNModC F (w * d)) := by sorry
