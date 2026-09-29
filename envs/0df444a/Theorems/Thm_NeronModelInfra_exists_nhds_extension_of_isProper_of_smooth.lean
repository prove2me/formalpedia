-- Prove2me | Theorems.Thm_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth
-- name    : NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/0ad39eb7-8481-5656-92c3-271cd744eb65
-- title:
--   Extension across a maximal point of the special fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with `IsDiscreteValuationRing`) and let $K$ be a field which is an $R$-algebra and a fraction field of $R$; write $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for `specGenericFibreInclusion R K`, the morphism $\operatorname{Spec}$ of the structure map $R \to K$. Let $X$ and $T$ be schemes, $f \colon X \to \operatorname{Spec} R$ a proper morphism, and $t \colon T \to \operatorname{Spec} R$ a smooth and quasi-compact morphism. Let $u_K$ be a morphism of the generic fibres over $\operatorname{Spec} K$, that is, a morphism $T \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ whose composite with the second projection of the pullback of $f$ and $\iota$ is the second projection of the pullback of $t$ and $\iota$. Let $\eta \in T$ be a point lying over the closed point of $\operatorname{Spec} R$ such that every $y \in T$ with $\eta$ in the closure of $\{y\}$ and with $y$ lying over the closed point equals $\eta$ (so $\eta$ is a maximal point of the special fibre). Then there are an open subscheme $U \subseteq T$ containing $\eta$ and a morphism $g \colon U \to X$ with $g$ followed by $f$ equal to the open immersion $U \to T$ followed by $t$, such that the induced morphism on generic fibres $U \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (namely `genericFibreRestrict`, the lift of the first projection followed by $g$ and of the second projection) coincides with the canonical morphism $U \times_{\operatorname{Spec} R} \operatorname{Spec} K \to T \times_{\operatorname{Spec} R} \operatorname{Spec} K$ induced by the open immersion and the identity on $\operatorname{Spec} K$, followed by $u_K$.
--
--   This is the local form, at a single maximal point of the special fibre, of the first step of the extension argument of Bosch–Lütkebohmert–Raynaud, Néron Models, Proposition 1.2/8 (Weil's extension of a generic-fibre morphism into a proper scheme across codimension one), the local ring at such a point being a discrete valuation ring when $T$ is smooth over $R$. It is used by [`NeronModelInfra.exists_opens_extension_of_isProper_of_smooth`](thm.html#NeronModelInfra.exists_opens_extension_of_isProper_of_smooth), which globalises the conclusion over the maximal points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by sorry
