-- Prove2me | Theorems.Thm_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
-- name    : NeronModelInfra.isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/adca28c9-5544-52b1-8740-16c67c43084e
-- title:
--   Scheme-theoretic image of the generic-fibre diagonal over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, and let $K$ be a field that is a fraction field of $R$; write $\iota_K \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for `specGenericFibreInclusion R K`, the morphism $\operatorname{Spec}$ of the structure map $R \to K$. Let $g_K \colon X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact, and let $f_1 \colon Y_1 \to \operatorname{Spec} R$, $f_2 \colon Y_2 \to \operatorname{Spec} R$ each be smooth, separated, locally of finite type and quasi-compact. For $\nu = 1,2$ let $e_\nu$ be a morphism from the fibre product $Y_\nu \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ whose composite with $g_K$ is the projection to $\operatorname{Spec} K$ (an element of the subtype `SchemeHomOver`), with $e_1$ an open immersion and $e_2$ an isomorphism. Let $\delta$ be a morphism from the fibre product of $e_1$ and $e_2$ to $Y_1 \times_{\operatorname{Spec} R} Y_2$ whose composites with the two projections of the latter are the two projections of the former followed by the projections to $Y_1$, resp. $Y_2$. Then: the morphism $\delta$ followed by the canonical closed immersion of its scheme-theoretic image, `δ.toImage`, is an open immersion; the set of points of that image in the range of `δ.toImage` is exactly the set of $d$ whose image under the closed immersion `δ.imageι`, then the first projection, then $f_1$, is not the closed point of $\operatorname{Spec} R$; and the range of `δ.imageι` on points is the closure of the range of $\delta$ on points.
--
--   This is the standard description of the schematic closure of the generic-fibre diagonal $\Delta_K = (Y_1)_K \times_{X_K} (Y_2)_K$ inside $Y_1 \times_R Y_2$: its part over the generic point of $\operatorname{Spec} R$ is $\Delta_K$ itself, and its underlying space is the topological closure of the image of $\delta$. It is used in the Néron-model comparison step, where it feeds the criterion that a point fails to lie in the closure of the image when no extension of a section exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) :
    IsOpenImmersion δ.toImage ∧
      Set.range δ.toImage.base =
        {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R} ∧
      Set.range δ.imageι.base = closure (Set.range δ.base) := by sorry
