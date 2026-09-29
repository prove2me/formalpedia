-- Prove2me | Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
-- name    : NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/05699e3a-9f7e-545b-b826-e2f68561feea
-- title:
--   Gluing smooth R-models along a common generic fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring) with fraction field $K$, and write $\iota_{R,K} : \operatorname{Spec} K \to \operatorname{Spec} R$ for `specGenericFibreInclusion R K`, the morphism induced by the structure map $R \to K$. Let $g_K : X_K \to \operatorname{Spec} K$ be separated, locally of finite type and quasi-compact, and let $\iota$ be a finite non-empty index type with schemes $Y_i$ and morphisms $f_i : Y_i \to \operatorname{Spec} R$ such that each $f_i$ is smooth, separated, locally of finite type and quasi-compact. For each $i$ let $e_i$ be a morphism from the generic fibre $\operatorname{pullback}(f_i, \iota_{R,K})$ to $X_K$ with $e_i$ followed by $g_K$ equal to the second projection (so $e_i$ is a $K$-morphism), and assume each $e_i$ is an isomorphism. Assume further that for all $i \neq j$, every morphism $\delta : \operatorname{pullback}(e_i, e_j) \to \operatorname{pullback}(f_i, f_j)$ whose composites with the two projections to $Y_i$ and $Y_j$ agree with the projections of $\operatorname{pullback}(e_i,e_j)$ followed by the first projections of the generic fibres of $f_i$, resp. $f_j$, is a closed immersion. Then there exist a scheme $X$, a morphism $g : X \to \operatorname{Spec} R$, a morphism $e_X$ from the generic fibre $\operatorname{pullback}(g, \iota_{R,K})$ to $X_K$ over $\operatorname{Spec} K$, and morphisms $j_i : Y_i \to X$ with $j_i$ followed by $g$ equal to $f_i$, such that $g$ is smooth, separated, locally of finite type and quasi-compact, $e_X$ is an isomorphism, each $j_i$ is an open immersion, the induced map on generic fibres `genericFibreRestrict R K g (f i) (j i)` followed by $e_X$ equals $e_i$ for every $i$, and every point of $X$ lies in the image of the underlying map of some $j_i$.
--
--   This is the gluing step in the construction of Néron models over a discrete valuation ring (Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4(ii)): finitely many smooth separated $R$-models of one and the same separated $K$-scheme of finite type, whose pairwise diagonals are closed, may be glued to a single smooth separated $R$-model covered by them. It is used by [`NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension`](thm.html#NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension), and its proof appeals to the gluing principle [`AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion`](thm.html#AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion) for schemes glued along a common open subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (hdiag : ∀ i j, i ≠ j → ∀ δ : pullback (e i).1 (e j).1 ⟶ pullback (f i) (f j),
      δ ≫ pullback.fst (f i) (f j) = pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K) →
      δ ≫ pullback.snd (f i) (f j) = pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K) →
      IsClosedImmersion δ) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (j : ∀ i, SchemeHomOver (f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g (f i) (j i)).1 ≫ eX.1 = (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by sorry
