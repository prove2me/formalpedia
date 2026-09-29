-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing
-- name    : ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/b084fa4b-3f61-569d-9fc7-6765a47a54be
-- title:
--   Crossing points specialise from both component generic points
-- statement:
--   Fix a prime $p$, a package $\mathfrak{X} : \mathrm{DRModelPackage}\ p$ for the Deligne–Rapoport integral model of the modular curve, a commutative ring $O$, an algebraically closed field $\kappa$ of characteristic $p$, and a ring homomorphism $t \colon O \to \kappa$. Write $b =$ `DRModel.baseChangeMap t` for the morphism $\mathrm{DRModel}(p) \times_{\mathbb{Z}} \operatorname{Spec}\kappa \to \mathrm{DRModel}(p) \times_{\mathbb{Z}} \operatorname{Spec}O$ obtained from the pullback of the structure map to $\operatorname{Spec}\mathbb{Z}$ by base change along $\operatorname{Spec} t$ (identity on the first factor). Let $i_\infty = \mathfrak{X}.\mathtt{compInf}\ \kappa$ and $i_0 = \mathfrak{X}.\mathtt{compZero}\ \kappa$ be the two component morphisms out of the curve $(\mathfrak{X}.\mathtt{ratModel}\ \kappa).C$, with $\eta$ its generic point, and let $n$ be a point of the scheme-theoretic fibre product of $i_\infty$ and $i_0$. Setting $x_n$ to be the image of $n$ under the first projection followed by $i_\infty$ followed by $b$, the assertion is the conjunction of the two specialisation relations $b(i_\infty(\eta)) \rightsquigarrow x_n$ and $b(i_0(\eta)) \rightsquigarrow x_n$ between points of the topological space of the $O$-model.
--
--   This records that each crossing point of the special fibre of the base-changed Deligne–Rapoport model lies in the closure of the images of the generic points of both crossing components; the two specialisation relations are exactly the data needed to define the two branch ideals at a crossing point as pullbacks of maximal ideals along specialisation maps. It is used in the construction of oriented crossing charts, in [`ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart`](thm.html#ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart) and in downstream statements about crossing points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n ∧
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n := by sorry
