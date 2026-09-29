-- Prove2me | Theorems.Thm_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
-- name    : NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3b204413-b4db-5a41-8c35-d814fd5f7afc
-- title:
--   Closure of the generic diagonal misses the special fibre's generic point
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, and let $g_K \colon X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact. Let $f_1 \colon Y_1 \to \operatorname{Spec} R$ and $f_2 \colon Y_2 \to \operatorname{Spec} R$ be given, each assumed (as a conjunction of four conditions) smooth, separated, locally of finite type and quasi-compact. Write $\operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by $R \to K$; for $\nu = 1,2$ let $e_\nu$ be a morphism from the generic fibre $Y_\nu \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ commuting with the projection to $\operatorname{Spec} K$ and $g_K$, and assume each $e_\nu$ is an isomorphism. Let $\xi_1 \in Y_1$ lie over the closed point of $R$ and specialise to every point of $Y_1$ lying over the closed point. Assume that for every open $U \subseteq Y_1$ containing $\xi_1$ and every morphism $u \colon U \to Y_2$ with $u \circ f_2 = \iota_U \circ f_1$ (diagrammatic order), the induced morphism of generic fibres $U_K \to (Y_2)_K$ followed by $e_2$ differs from the morphism $U_K \to (Y_1)_K$ induced by $\iota_U$ followed by $e_1$. Finally let $\delta \colon (Y_1)_K \times_{X_K} (Y_2)_K \to Y_1 \times_{\operatorname{Spec} R} Y_2$ be a morphism whose composites with the two projections $\mathrm{pr}_1, \mathrm{pr}_2$ agree with the projections of $(Y_1)_K \times_{X_K} (Y_2)_K$ followed by $(Y_\nu)_K \to Y_\nu$. Then $\xi_1$ does not lie in the closure of the image under $\mathrm{pr}_1$ of the intersection of the closure of the range of $\delta$ on points with the set of points of $Y_1 \times_{\operatorname{Spec} R} Y_2$ whose image under $\mathrm{pr}_1$ lies over the closed point of $R$.
--
--   This is the nowhere-density step in the comparison of two smooth separated $R$-models of one $K$-scheme (Bosch–Lütkebohmert–Raynaud, Néron Models, 4.3, Proposition 4(i)): the special-fibre part of the closure of the graph of $e_2^{-1}e_1$ avoids the generic point $\xi_1$ of the special fibre of $Y_1$ whenever $e_1$ extends over no neighbourhood of $\xi_1$. It is obtained from the variant [`NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral`](thm.html#NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral), which assumes $Y_1$ integral and only that $e_1$ be an open immersion, using openness of irreducible components of schemes with integral stalks, and it feeds into [`NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension`](thm.html#NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra

universe u

theorem NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsIso e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (hne : ∀ (U : Y₁.Opens), ξ₁ ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f₁) f₂,
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) :
    ξ₁ ∉ closure ((pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩
        {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R})) := by sorry
