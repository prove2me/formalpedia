-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension
-- name    : NeronModelInfra.exists_opens_extension_of_forall_nhds_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/99eb3db2-e19b-559d-807e-f1ab49870a0a
-- title:
--   Gluing neighbourhood extensions over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure) and let $K$ be a field which is an $R$-algebra and a fraction field of $R$; write $i\colon\operatorname{Spec}K\to\operatorname{Spec}R$ for the morphism `specGenericFibreInclusion` induced by $R\to K$. Let $f\colon X\to\operatorname{Spec}R$ be separated and $t\colon T\to\operatorname{Spec}R$ smooth and quasi-compact, and let $u_K$ be a morphism $T\times_{\operatorname{Spec}R}\operatorname{Spec}K\to X\times_{\operatorname{Spec}R}\operatorname{Spec}K$ commuting with the two second projections, i.e. a $K$-morphism of generic fibres. Assume: for every point $\eta$ of $T$ lying over the closed point of $R$ such that the only point $y$ of $T$ over the closed point with $\eta$ in the closure of $\{y\}$ is $\eta$ itself (so $\eta$ is a generic point of the special fibre), there are an open $U\subseteq T$ with $\eta\in U$ and a morphism $g\colon U\to X$ with $g$ followed by $f$ equal to $U\hookrightarrow T$ followed by $t$, whose base change to $\operatorname{Spec}K$ equals the canonical map $U_K\to T_K$ followed by $u_K$. Then there are an open $V\subseteq T$ and a morphism $v\colon V\to X$ over $\operatorname{Spec}R$ such that $V$ contains every point of $T$ not lying over the closed point of $R$, $V$ meets every irreducible component of the subspace of points lying over the closed point, and the base change of $v$ to $\operatorname{Spec}K$ equals the canonical map $V_K\to T_K$ followed by $u_K$.
--
--   This is the gluing step in the construction of Néron models over a discrete valuation ring (Bosch–Lütkebohmert–Raynaud 1.2/8, 7.1/1): local extensions of a generic-fibre morphism at the generic points of the special fibre, assumed here rather than produced by a valuative criterion or by graph closure, are patched — using separatedness of $f$ through the injectivity of generic-fibre restriction — into a single extension over an open subscheme containing the generic fibre and meeting every component of the special fibre. It is used in the extension of group laws, of translations and of twists, and hence in the Néron criterion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.exists_opens_extension_of_forall_nhds_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (hloc : ∀ η : T, t.base η = IsLocalRing.closedPoint R →
      (∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
        (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
          pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by sorry
