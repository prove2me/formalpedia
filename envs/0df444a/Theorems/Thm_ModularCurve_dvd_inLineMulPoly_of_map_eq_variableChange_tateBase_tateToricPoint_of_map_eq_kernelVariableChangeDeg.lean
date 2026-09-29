-- Prove2me | Theorems.Thm_ModularCurve_dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg
-- name    : ModularCurve.dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/48158a14-5539-5ecc-921a-91ce49a75d82
-- title:
--   Tate-curve divisibility of the level kernel into `inLineMulPoly`
-- statement:
--   Let $F$ be a field of characteristic zero, $q$ a nonzero natural number, $\ell \neq 2$ a prime, $k \geq 1$, and $c \in F^{\times}$ a unit whose image in $F$ is a primitive $\ell$-th root of unity; let $C$ be a Weierstrass variable change over the Laurent series field $\mathrm{LaurentSeries}\,F$. Let $T$ be a field with a ring homomorphism $\varphi : T \to \mathrm{LaurentSeries}\,F$, let $W$ be a Weierstrass curve over $T$, let $D$ be a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43) over $T$, i.e. a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $T$, and let $h \in T[X]$. Assume: (i) $W$ pushed forward along $\varphi$ is $C \bullet \mathrm{tateBase}\,F\,q$, the Tate curve over $\mathrm{LaurentSeries}\,F$ with the exponent-scaling substitution `qExpand` by $q$ applied, acted on by $C$; (ii) the quadruple obtained by applying $\varphi$ to the four entries of $D$ equals the `variableChange` by $C$ (i.e. $x \mapsto u^{-2}(x - r)$, $y \mapsto u^{-3}(y - s(x-r) - t)$ applied to both points) of the quadruple whose two points are both equal to $\mathrm{tateToricPoint}\,F\,q\,c$, the explicit Tate-parametrised point attached to $c$; (iii) for every field $F'$, every ring homomorphism $f : F \to F'$ and every primitive $\ell^k$-th root of unity $\zeta \in F'$, the image of $h$ under $\varphi$ followed by the coefficientwise map [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16) equals $\mathrm{kernelVariableChangeDeg}$ of $C$ mapped by `coeffMap f`, with degree parameter $\mathrm{gamma0PowDeg}\,\ell\,k$ (namely $1$ if $\ell^k = 2$, otherwise $\varphi(\ell^k)/2$), applied to $\prod_{1 \le a \le \ell^k/2,\ \ell \nmid a} \bigl(X - x(\mathrm{toricPoint}\,F'\,q\,(\zeta^a))\bigr)$; here $\mathrm{kernelVariableChangeDeg}\,C\,d\,g = u^{-2d} \cdot g(u^2 X + r)$. The conclusion is that in $T[X]$ the polynomial $h$ divides $\mathrm{inLineMulPoly}\,W\,\ell\,(\ell^{k-1})\,x_P$, that is the product over $1 \le a \le (\ell-1)/2$ of $\Phi_{\ell^{k-1}} \cdot (\Psi^2_a)(x_P) - (\Phi_a)(x_P) \cdot \Psi^2_{\ell^{k-1}}$.
--
--   This is the Tate-curve (cusp) instance of the divisibility expressing that the roots of the level-structure kernel polynomial $h$ are $x$-coordinates of points $G$ with $[\ell^{k-1}]G$ a non-trivial multiple of the toric $\ell$-torsion point, stated over a field $T$ mapping to the Laurent series field so that it can be applied after descent. It is used in the construction of points and variable changes on the full-level curves in the $H_1$ column at the Tate parameter, in particular by the existence statements [`ModularCurve.FullLevel.Diamond.exists_variableChange_raw_etale_tate_weightOne_level_fst_level_snd_fst_of_ker`](thm.html#ModularCurve.FullLevel.Diamond.exists_variableChange_raw_etale_tate_weightOne_level_fst_level_snd_fst_of_ker), [`ModularCurve.FullLevel.Diamond.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow) and [`ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_rigidDataH1Pow_of_algebra_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_rigidDataH1Pow_of_algebra_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg
    (F : Type) [Field F] [CharZero F] (q : ℕ) [NeZero q]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (k : ℕ) (hk : 1 ≤ k)
    (c : Fˣ) (hc : IsPrimitiveRoot (c : F) ℓ)
    (C : WeierstrassCurve.VariableChange (LaurentSeries F))
    (T : Type) [Field T] (φ : T →+* LaurentSeries F)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T) (h : Polynomial T)
    (hW : W.map φ = C • ModularCurve.tateBase F q)
    (hD : D.map φ = ((⟨(ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2,
            (ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries F)).variableChange C))
    (hh : ∀ (F' : Type) [Field F'] (f : F →+* F') (ζ : F'), IsPrimitiveRoot ζ (ℓ ^ k) →
      (h.map φ).map (ModularCurve.coeffMap f) =
        ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f)) (ModularCurve.gamma0PowDeg ℓ k)
          (∏ a ∈ (Finset.Icc 1 (ℓ ^ k / 2)).filter (fun a => ¬ ℓ ∣ a),
            (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) :
    h ∣ ModularCurve.inLineMulPoly W ℓ (ℓ ^ (k - 1)) D.xP := by sorry
