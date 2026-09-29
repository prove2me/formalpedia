-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
-- name    : ModularCurve.DRLevel.mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/1f36fb78-d725-57d3-8fd8-02fa99e75d8a
-- title:
--   Regularity of j forces a point into the finite chart
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$, a field $\kappa$ and a ring homomorphism $\mathrm{to}\kappa : R\,q \to \kappa$ from the base ring $R\,q$ of the Igusa scheme. Let $M$ be a `CurveModel` for $\kappa$ and the field $\mathrm{modularFunctionFieldC}\,\kappa\,N_0 = \kappa(\mathrm{jqModC}\,\kappa,\ \mathrm{jqModC}_{N_0}\,\kappa)\subseteq \mathrm{LaurentSeries}\,\kappa$, that is: an integral scheme `M.C`, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$, a ring isomorphism `M.ffEquiv` of that field with the function field of `M.C` over $\kappa$, and a bijection `M.placeOfPoint` from the closed points of `M.C` to the places of the field over $\kappa$ matching stalks with valuation subrings. Let $e :$ `M.C` $\to$ `fibre0 toκ` be a morphism into the fibre product of `toBase0 N₀ q` $:$ `X0 N₀ q` $\to \operatorname{Spec}(R\,q)$ with $\operatorname{Spec}(\mathrm{to}\kappa)$, and write $\varphi$ for $e$ followed by the first projection, so $\varphi :$ `M.C` $\to$ `X0 N₀ q`. Assume (i) the open subscheme $\varphi^{-1}$ of the image of the finite chart $\iota_{\mathrm{fin}} =$ `IgusaScheme.ιFin N₀ q` under the whole space is non-empty; (ii) a normalisation of the chart: for every $b$ in the subalgebra `chartAlgFin N₀ q` of `modularFunctionFieldFull N₀`, letting $\mathrm{read}\,b$ be the element of $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ obtained by transporting $b$ through the global-sections isomorphism of $\operatorname{Spec}$ of that subalgebra, the isomorphism of $\iota_{\mathrm{fin}}$ on sections over the whole space, the map $\varphi$ on sections over the above open, the germ into the function field of `M.C`, and `M.ffEquiv.symm`, one has $\mathrm{read}\,b =$ `jGeomGen κ N₀` when $b =$ `jChartFin N₀ q`, and $\mathrm{read}\,b =$ `jNGeomGen κ N₀` when the Laurent series underlying $b$ equals `qExpand ℚ N₀ jq`. Then for every closed point $x$ of `M.C` such that `jGeomGen κ N₀` lies in the valuation subring of the place `M.placeOfPoint x`, the image $\varphi(x)$ in the underlying space of `X0 N₀ q` lies in the range of the underlying map of $\iota_{\mathrm{fin}}$.
--
--   This is the statement that a point of the model at which the generator $j$ is regular for the associated place is not a cusp: it is carried by the affine chart of the Igusa scheme on which $j$ is a function, rather than by the chart around the pole of $j$. It is used in the identification of places of the special fibre with points of the chart, in [`ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq`](thm.html#ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRLevel.mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ)
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))
    (x : closedPoints M.C) (hj : jGeomGen κ N₀ ∈ (M.placeOfPoint x).toValuationSubring) :
    (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base x.1 ∈
      Set.range (IgusaScheme.ιFin N₀ q).base := by sorry
