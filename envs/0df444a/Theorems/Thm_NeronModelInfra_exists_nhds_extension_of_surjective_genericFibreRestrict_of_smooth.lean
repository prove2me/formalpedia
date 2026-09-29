-- Prove2me | Theorems.Thm_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth
-- name    : NeronModelInfra.exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/96b74956-5986-5352-ae2f-0be1a8fed073
-- title:
--   Néron criterion, local step: extension near a maximal point
-- statement:
--   Let $R$ be a discrete valuation ring which is an integral domain and a henselian local ring with algebraically closed residue field, and let $K$ be a field that is the fraction field of $R$ (via the given $R$-algebra structure); write $\iota\colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism `specGenericFibreInclusion` induced by $R \to K$. Let $X$, $T$ be schemes and $f\colon X \to \operatorname{Spec} R$ a separated, locally of finite type, quasi-compact morphism. Assume that the map `genericFibreRestrict R K f (𝟙 _)` is surjective: every morphism $\psi$ from the fibre product of $\mathrm{id}_{\operatorname{Spec} R}$ with $\iota$ to the fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ that commutes with the second projections arises, in the canonical way, from a section $s\colon \operatorname{Spec} R \to X$ of $f$; informally, every $K$-point of $X_K$ extends to an $R$-point of $X$. Let $t\colon T \to \operatorname{Spec} R$ be smooth and quasi-compact, and let $u_K$ be a morphism $T \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ compatible with the second projections to $\operatorname{Spec} K$. Let $\eta \in T$ be a point lying over the closed point of $\operatorname{Spec} R$ such that the only point $y$ of $T$ over the closed point with $y \rightsquigarrow \eta$ is $\eta$ itself (so $\eta$ is a maximal point of the special fibre). Then there are an open subscheme $U \subseteq T$ with $\eta \in U$ and a morphism $g\colon U \to X$ with $g \circ \,$ (i.e. $U \hookrightarrow T$ followed by $t$) equal to $f \circ g$ — that is, an $R$-morphism $g$ over $U \hookrightarrow T \to \operatorname{Spec} R$ — whose generic-fibre base change $U \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ equals the canonical map induced by $U \hookrightarrow T$ over the identities of $\operatorname{Spec} K$ and $\operatorname{Spec} R$, followed by $u_K$; in other words $g_K$ is the restriction of $u_K$ to $U_K$.
--
--   This is the local step in Néron's criterion (the implication that surjectivity of $X(R) \to X_K(K)$ yields the weak Néron mapping property at a smooth test scheme $T$), giving extension of a given $K$-morphism only on a neighbourhood of one maximal point of the special fibre; no group structure on $X$ is involved. It is used in the construction of the Néron model property bundle, [`NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian`](thm.html#NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian), where such local extensions are glued and then assembled with Weil's extension theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hext : Function.Surjective (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))))
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by sorry
