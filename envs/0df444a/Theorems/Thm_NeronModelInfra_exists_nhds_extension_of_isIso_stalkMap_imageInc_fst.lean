-- Prove2me | Theorems.Thm_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
-- name    : NeronModelInfra.exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d27fe683-a219-5a97-9ab3-c8c47fa2aace
-- title:
--   Extending the generic-fibre map near a special point
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), $K$ a field that is a fraction field of $R$ via a given $R$-algebra structure, and write $\iota_K \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by $R \to K$ (`specGenericFibreInclusion`). Let $g_K \colon X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact, and let $f_1 \colon Y_1 \to \operatorname{Spec} R$, $f_2 \colon Y_2 \to \operatorname{Spec} R$ each be smooth, separated, locally of finite type and quasi-compact. Generic fibres are taken as the pullbacks along $\iota_K$, with structure morphism the second projection. Assume given $e_1$, a morphism from the generic fibre of $f_1$ to $X_K$ commuting with the projections to $\operatorname{Spec} K$ and with $e_1$ an open immersion, and $e_2$, likewise over $\operatorname{Spec} K$ for $f_2$, with $e_2$ an isomorphism. Let $\xi_1 \in Y_1$ lie over the closed point of $R$. Assume given a morphism $\delta \colon Y_{1,K} \times_{X_K} Y_{2,K} \to Y_1 \times_{\operatorname{Spec} R} Y_2$ compatible with both projections, namely $\delta$ followed by $\mathrm{pr}_i$ equals the $i$-th projection of the pullback of $e_1,e_2$ followed by the projection of the generic fibre of $f_i$ onto $Y_i$ ($i=1,2$); assume the morphism from this pullback onto the scheme-theoretic image $\delta.\mathrm{image}$ is an open immersion, and that its set-theoretic range is exactly the set of points of $\delta.\mathrm{image}$ whose image in $Y_1$, under the image inclusion followed by the first projection, does not lie over the closed point of $R$. Finally let $\eta$ be a point of $\delta.\mathrm{image}$ mapping to $\xi_1$ under the image inclusion followed by the first projection, and assume the stalk map of that composite at $\eta$ is an isomorphism. Then there are an open subscheme $U \subseteq Y_1$ containing $\xi_1$ and a morphism $u \colon U \to Y_2$ with $u$ followed by $f_2$ equal to the inclusion $U \hookrightarrow Y_1$ followed by $f_1$, such that on generic fibres the induced morphism $U_K \to Y_{2,K}$ followed by $e_2$ agrees with the induced morphism $U_K \to Y_{1,K}$ (from the open inclusion) followed by $e_1$.
--
--   This is the spreading-out step in the construction of Néron models (Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4(i)): from an isomorphism of local rings at a point of the schematic closure of the generic-fibre graph one obtains an extension of the birational map $e_2^{-1} e_1$ to a neighbourhood of a point $\xi_1$ of the special fibre. The spreading-out of the stalk isomorphism to an open immersion uses [`AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType`](thm.html#AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType), and the result feeds into [`NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral`](thm.html#NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral). Note that $e_1$ is required only to be an open immersion, which is the situation after shrinking $Y_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K))
    (hopen : IsOpenImmersion δ.toImage)
    (hlocus : Set.range δ.toImage.base =
      {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R})
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁)
    (hiso : IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η)) :
    ∃ (U : Y₁.Opens) (_ : ξ₁ ∈ U) (u : SchemeHomOver (U.ι ≫ f₁) f₂),
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 =
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1 := by sorry
