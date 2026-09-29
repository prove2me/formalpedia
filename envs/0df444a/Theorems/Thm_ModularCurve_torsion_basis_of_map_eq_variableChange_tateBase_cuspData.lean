-- Prove2me | Theorems.Thm_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData
-- name    : ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/c3d018be-67f9-58ee-9ff7-21767a961796
-- title:
--   Torsion basis at the Tate cusp pair of level q
-- statement:
--   Let $F$ be a field of characteristic zero, let $q$ be a prime, and let $\zeta$ be a unit of $F$ whose underlying element is a primitive $q$-th root of unity. Let $C$ be a Weierstrass variable change over the Laurent series field $\mathrm{LaurentSeries}\,F$, let $T$ be a field with a ring homomorphism $\varphi : T \to \mathrm{LaurentSeries}\,F$, let $W$ be a Weierstrass curve over $T$, and let $D$ be a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43) over $T$, that is, a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $T$. Assume that the curve obtained from $W$ by applying $\varphi$ to its coefficients equals $C \bullet \mathrm{tateBase}\,F\,q$, the action of $C$ on the Tate curve [`ModularCurve.tateBase`](def/ModularCurve_TateSlots.html#L46) (the Tate Weierstrass curve over Laurent series, with the exponent-scaling substitution by $q$ applied), and that applying $\varphi$ to the four coordinates of $D$ yields the image under $C$ of the cusp datum $\mathrm{cuspData}\,F\,q\,\zeta\,(1,0)\,(0,-1)$; the latter has $P$-coordinates the toric point `tateToricPoint` at $\zeta$ and $Q$-coordinates the non-toric point `nonToricPoint` at the unit $1$ with index $(-1 : \mathbb{Z}/q)$, and the action of $C$ on a level datum is the usual substitution $x \mapsto u^{-2}(x-r)$, $y \mapsto u^{-3}(y - s(x-r) - t)$. The conclusion asserts five things: $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$; writing $\mathrm{toPoint}\,W\,x\,y$ for the affine point $(x,y)$ when it is nonsingular and for the point at infinity otherwise, both $q \cdot \mathrm{toPoint}\,W\,x_P\,y_P$ and $q \cdot \mathrm{toPoint}\,W\,x_Q\,y_Q$ vanish in the group of affine points; and for all natural numbers $a,b < q$, if $a \cdot \mathrm{toPoint}\,W\,x_P\,y_P + b \cdot \mathrm{toPoint}\,W\,x_Q\,y_Q = 0$ then $a = b = 0$.
--
--   This supplies, for every prime $q$ including $q = 2$, the three conditions — lying on the curve, being killed by $q$, and being $\mathbb{Z}/q$-independent — that make the transported cusp pair of the Tate curve a Drinfeld basis of level $q$, descended from the Laurent series field to $T$ along $\varphi$. It is used in the construction of points of the full-level modular curve attached to the Tate curve and its rigid Weierstrass data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData.lean

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

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve
open scoped MatrixGroups
open scoped Classical in

theorem ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData
    (F : Type) [Field F] [CharZero F] (q : ℕ) [Fact q.Prime]
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) q)
    (C : WeierstrassCurve.VariableChange (LaurentSeries F))
    (T : Type) [Field T] (φ : T →+* LaurentSeries F)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T)
    (hW : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      W.map φ = C • ModularCurve.tateBase F q)
    (hD : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      D.map φ = (ModularCurve.cuspData F q ζ ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C) :
    W.toAffine.Equation D.xP D.yP ∧ W.toAffine.Equation D.xQ D.yQ ∧
    (q : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = 0 ∧
    (q : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 ∧
    (∀ a b : ℕ, a < q → b < q →
      (a : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP +
        (b : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 → a = 0 ∧ b = 0) := by sorry
