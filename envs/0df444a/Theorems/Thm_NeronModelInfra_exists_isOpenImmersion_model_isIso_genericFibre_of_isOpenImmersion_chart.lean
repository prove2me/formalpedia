-- Prove2me | Theorems.Thm_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
-- name    : NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/ec8b8658-9b28-54d2-9849-be8ce366fbaa
-- title:
--   Extending an R-model across the generic fibre
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, and write $\iota\colon \operatorname{Spec} K \to \operatorname{Spec} R$ for `specGenericFibreInclusion`, the morphism induced by $R \to K$. Let $g_K\colon X_K \to \operatorname{Spec} K$ and $f\colon Y \to \operatorname{Spec} R$ be separated, locally of finite type and quasi-compact, and let $q$ be a morphism from the fibre product $Y \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ that is an open immersion and satisfies $q \,;\, g_K = \mathrm{pr}_2$, i.e. is a morphism of $K$-schemes. Then there exist a scheme $Y'$, a morphism $f'\colon Y' \to \operatorname{Spec} R$, a morphism $j\colon Y \to Y'$ with $j \,;\, f' = f$, and a $K$-morphism $e\colon Y' \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X_K$ (so $e \,;\, g_K = \mathrm{pr}_2$) such that: $j$ is an open immersion; $f'$ is separated, locally of finite type and quasi-compact; $e$ is an isomorphism; every point $y'$ of $Y'$ whose image under $f'$ is the closed point of $\operatorname{Spec} R$ lies in the image of $j$; the composite of the base change $j_K$ of $j$ to generic fibres (given by `genericFibreRestrict`) with $e$ equals $q$; and if both $g_K$ and $f$ are smooth, then $f'$ is smooth.
--
--   This is the standard completion construction for models over a discrete valuation ring: an $R$-model of an open part of $X_K$ is enlarged, by gluing $X_K$ onto $Y$ along the open immersion $q$ of generic fibres, to an $R$-model whose generic fibre is all of $X_K$ and whose special fibre is unchanged. It is used in the construction of minimal models, being cited by [`NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints`](thm.html#NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1] :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ Y') (hj : j ≫ f' = f)
      (e : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK),
      IsOpenImmersion j ∧ IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsIso e.1 ∧
      (∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base) ∧
      schemeHomOverComp (genericFibreRestrict R K f' f ⟨j, hj⟩) e = q ∧
      (Smooth gK → Smooth f → Smooth f') := by sorry
