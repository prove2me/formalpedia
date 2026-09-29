-- Prove2me | Theorems.Thm_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq
-- name    : NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/66423544-ce85-5106-88cd-d21ed8029e4d
-- title:
--   Stalk isomorphism for the first projection on the schematic image
-- statement:
--   Let $R$ be a discrete valuation ring (a domain) with fraction field $K$, and write $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by the structure map $R \to K$. Let $g_K \colon X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact, and let $f_1 \colon Y_1 \to \operatorname{Spec} R$, $f_2 \colon Y_2 \to \operatorname{Spec} R$ each be smooth, separated, locally of finite type and quasi-compact (these four properties are bundled as the hypotheses $h_{f_1}$, $h_{f_2}$). Assume given morphisms $e_1$ from the pullback $Y_1 \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ and $e_2$ from $Y_2 \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$, each commuting with the projections to $\operatorname{Spec} K$ and $g_K$, with $e_1$ an open immersion and $e_2$ an isomorphism. Assume $Y_1$ integral, and let $\xi_1 \in Y_1$ lie over the closed point of $\operatorname{Spec} R$ and specialise to every point of $Y_1$ lying over that closed point. Let $\delta \colon (Y_1)_K \times_{X_K} (Y_2)_K \to Y_1 \times_{\operatorname{Spec} R} Y_2$ be a morphism whose composites with the two projections to $Y_1$ and $Y_2$ are the two projections of the pullback of $e_1$ and $e_2$ followed by the projections $(Y_i)_K \to Y_i$ (these two conditions determine $\delta$, the projections being jointly monic). Finally let $\eta$ be a point of the scheme-theoretic image $\overline{\Delta}$ of $\delta$ whose image under $\overline{\Delta} \hookrightarrow Y_1 \times_{\operatorname{Spec} R} Y_2 \to Y_1$ is $\xi_1$. Then the stalk map of this composite at $\eta$, that is $\mathcal{O}_{Y_1,\xi_1} \to \mathcal{O}_{\overline{\Delta},\eta}$, is an isomorphism.
--
--   This is the local domination step in the comparison of two smooth separated $R$-models of a $K$-scheme, as in Bosch–Lütkebohmert–Raynaud's treatment of Néron models: over the generic point of the special fibre of $Y_1$ the first projection from the schematic image of the graph-type locus $\overline{\Delta}$ is an isomorphism on local rings. It is used by [`NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral`](thm.html#NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral), and the proof cites birationality of the first projection together with the discreteness of the valuation of the stalk $\mathcal{O}_{Y_1,\xi_1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    [IsIntegral Y₁]
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K))
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁) :
    IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η) := by sorry
