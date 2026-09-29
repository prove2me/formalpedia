-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth
-- name    : NeronModelInfra.exists_opens_extension_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/66206db8-2f8c-55c5-8ce0-5556b476976a
-- title:
--   Extension over an open meeting every component of the special fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` property) and let $K$ be a field that is an $R$-algebra and a fraction field of $R$; write $\operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism `specGenericFibreInclusion` induced by the structure map $R \to K$. Let $X, T$ be schemes, let $f : X \to \operatorname{Spec} R$ be proper, and let $t : T \to \operatorname{Spec} R$ be smooth and quasi-compact. Let $u_K$ be a morphism over $\operatorname{Spec} K$ from the fibre product of $t$ with $\operatorname{Spec} K \to \operatorname{Spec} R$ to that of $f$, i.e. a morphism whose composition with the second projection of the target pullback is the second projection of the source pullback. The assertion is that there are an open subscheme $V \subseteq T$ and a morphism $v : V \to X$ with $v$ followed by $f$ equal to the open immersion $V \hookrightarrow T$ followed by $t$, such that: every point $x$ of $T$ with $t(x)$ not the closed point of $R$ lies in $V$; every irreducible component of the subspace $\{x \in T : t(x) = \text{closed point}\}$ contains a point lying in $V$; and the base change of $v$ to $\operatorname{Spec} K$, as produced by `genericFibreRestrict`, equals the canonical morphism of pullbacks induced by $V \hookrightarrow T$ and the identity of $\operatorname{Spec} K$, followed by $u_K$.
--
--   This is the first step in the construction of a morphism extending a given one on generic fibres (the smooth, quasi-compact case of the argument via the valuative criterion of properness at the generic points of the special fibre, as in Bosch–Lütkebohmert–Raynaud 1.2/8): the extension is obtained not on all of $T$ but on an open set containing the generic fibre and meeting every irreducible component of the special fibre. It is used in the proof that restriction to generic fibres is surjective for quasi-compact smooth test schemes, via [`NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth`](thm.html#NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth) for the local extensions and [`NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated`](thm.html#NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated) for their agreement on overlaps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.exists_opens_extension_of_isProper_of_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by sorry
