-- Prove2me | Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
-- name    : NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/4663469b-d70e-5429-a877-7d6a0fae5ce0
-- title:
--   Gluing pairwise inequivalent smooth R-models into one model
-- statement:
--   Let $R$ be a discrete valuation ring (a domain) with fraction field $K$, and let $g_K \colon X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact. Let $\iota$ be a finite nonempty index type and, for each $i$, let $f_i \colon Y_i \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, equipped with $e_i$: a morphism from the fibre product $Y_i \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (the base change along $\operatorname{Spec}$ of $R \to K$) to $X_K$ commuting with the projections to $\operatorname{Spec} K$, whose underlying morphism is an isomorphism. Assume given points $\xi_i \in Y_i$ lying over the closed point of $\operatorname{Spec} R$ such that every point of $Y_i$ over the closed point is a specialisation of $\xi_i$, and assume that for $i \neq j$, every open $U \subseteq Y_i$ containing $\xi_i$ and every morphism $u \colon U \to Y_j$ over $\operatorname{Spec} R$ satisfy: the generic-fibre base change of $u$ followed by $e_j$ differs from the generic-fibre base change of the inclusion $U \hookrightarrow Y_i$ followed by $e_i$. Then there are a scheme $X$, a morphism $g \colon X \to \operatorname{Spec} R$ which is smooth, separated, locally of finite type and quasi-compact, a morphism $e_X$ from $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $\operatorname{Spec} K$ whose underlying morphism is an isomorphism, opens $V_i \subseteq Y_i$ and morphisms $j_i \colon V_i \to X$ over $\operatorname{Spec} R$, such that each $V_i$ contains $\xi_i$ and every point of $Y_i$ not over the closed point, each $j_i$ is an open immersion, the generic-fibre base change of $j_i$ followed by $e_X$ equals that of $V_i \hookrightarrow Y_i$ followed by $e_i$, and the images of the $j_i$ on points cover $X$.
--
--   This is the gluing step for Néron models: finitely many smooth separated $R$-models of a fixed $K$-scheme, each with irreducible special fibre (a point $\xi_i$ specialising to all points over the closed point) and pairwise inequivalent near those points, are glued along their common generic fibre into a single smooth separated model covered by open pieces of the given ones. It is used in the construction of a model capturing the relevant rational points, in the form cited by [`NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative`](thm.html#NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (V : ∀ i, (Y i).Opens) (j : ∀ i, SchemeHomOver ((V i).ι ≫ f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g ((V i).ι ≫ f i) (j i)).1 ≫ eX.1 =
        (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by sorry
