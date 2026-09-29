-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- name    : ModularCurve.DRModelPackage.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/44f2038b-2a53-5f4a-beb6-da47c61d8bd7
-- title:
--   Transversal parameters at a crossing are uniformisers on each branch
-- statement:
--   Fix a prime $p$ and a package $\mathfrak X$ of data and properties for the two-chart integral model `DRModel p` of the level-$p$ modular function field over $\mathbf Z$; let $O$ be a discrete valuation domain, $k$ an algebraically closed field of characteristic $p$, and $toκ : O \to k$ a ring homomorphism. Write $X_O$ for the base change $\mathrm{pullback}$ of `DRModel.toBase p` along $\operatorname{Spec}$ of $\mathbf Z \to O$, and $X_k$ for the corresponding base change along $\mathbf Z \to k$, with `DRModel.baseChangeMap toκ` the induced morphism $X_k \to X_O$. Let $C$ be the underlying scheme of the curve model $\mathfrak X.\mathrm{ratModel}\,k$ over $k$ (integral, proper, smooth of relative dimension $1$, with its isomorphism `ffEquiv` of the coefficient field onto the function field of $C$ and its bijection `placeOfPoint` from closed points to places), and let $\mathfrak X.\mathrm{compInf}\,k$, $\mathfrak X.\mathrm{compZero}\,k$ be the two morphisms $C \to X_k$ attached to the package. Given a point $n$ of their fibre product, with images $y_1$, $y_2$ in $C$ under the two projections, assume: $\{y_1\}$ and $\{y_2\}$ are closed; a point $x$ of $X_O$ is the image of $y_1$ under $\mathfrak X.\mathrm{compInf}\,k$ followed by `DRModel.baseChangeMap toκ`, and also the image of $y_2$ under $\mathfrak X.\mathrm{compZero}\,k$ followed by the same map; the images of the generic point of $C$ under these two composites both specialise to $x$. Let $u, v$ be elements of the stalk $R$ of $X_O$ at $x$ such that $(p,u,v)$ is the maximal ideal of $R$, while $(p,u)$ and $(p,v)$ are the contractions to $R$, along the specialisation maps on stalks, of the maximal ideals of the stalks at the two generic-point images. Assume further that the stalk maps of `DRModel.baseChangeMap toκ` at the points $\mathfrak X.\mathrm{compInf}\,k\,(y_1)$ and $\mathfrak X.\mathrm{compZero}\,k\,(y_2)$ each carry the maximal ideal to an ideal generating the maximal ideal. Then the order at the place `placeOfPoint` of $y_1$ (minus the logarithm of the adic valuation at the corresponding height-one prime) of the element obtained from $v$ by transporting along the stalk identification at $x$, applying the stalk map of $\mathfrak X.\mathrm{compInf}\,k$ followed by `DRModel.baseChangeMap toκ` at $y_1$, passing to the function field of $C$ and back through `ffEquiv`, equals $1$; and symmetrically the order at the place of $y_2$ of the element obtained in the same way from $u$ through $\mathfrak X.\mathrm{compZero}\,k$ equals $1$.
--
--   This is the statement that a transversal pair of parameters at a crossing of the fibre at $p$ of the Deligne–Rapoport model restricts to a uniformiser on each of the two branches through that crossing, the orders being computed in the rational curve model of the package. It is used in the analysis of node coordinates and of the widths of the crossings in the resolved model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open IsLocalRing

theorem ModularCurve.DRModelPackage.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (u v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x))
    (h𝔭₁ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _))
    (h𝔭₂ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _))

    (hunr₁ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _)
    (hunr₂ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom v)))) = 1 ∧
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₂)).hom.hom u)))) = 1 := by sorry
