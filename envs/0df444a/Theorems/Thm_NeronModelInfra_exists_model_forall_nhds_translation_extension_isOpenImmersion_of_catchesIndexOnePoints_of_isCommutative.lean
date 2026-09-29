-- Prove2me | Theorems.Thm_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
-- name    : NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/282d5e90-92cf-5cde-ba3d-26b030e960ca
-- title:
--   Translation-extending R-model from a weak Néron model, commutative case
-- statement:
--   Let $R$ be a discrete valuation ring (a domain) with fraction field $K$, and let $g_K \colon X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact, equipped with a relative group law $L_{X_K}$ — a functorial group structure on the sets of $K$-morphisms $T \to X_K$ over $K$, natural in $T$ — assumed commutative. Let $M$ be a model family for $g_K$: a type $\iota$, assumed finite, of $R$-schemes $X_i \to \operatorname{Spec} R$ together with open immersions of the generic fibres $(X_i)_K \to X_K$ over $K$, each $X_i \to \operatorname{Spec} R$ being smooth, separated, locally of finite type and quasi-compact; assume $M$ catches index-one points, i.e. for every discrete valuation ring $R'$ that is a local $R$-algebra with $\mathfrak m_R R' = \mathfrak m_{R'}$ and formally smooth residue field extension, with fraction field $K'$ compatibly over $K$, every $K'$-point of $X_K$ over $K$ is the generic fibre of an $R'$-point of some $X_i$ followed by the chart. Then there exist a scheme $X$, a morphism $f \colon X \to \operatorname{Spec} R$ that is smooth, separated, locally of finite type and quasi-compact, whose fibre over the closed point of $\operatorname{Spec} R$ contains a point, and a morphism $e$ from the generic fibre $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $K$ which is an isomorphism, such that the following two assertions hold. For every scheme $Z$ with $z \colon Z \to \operatorname{Spec} R$ smooth and quasi-compact, every $K$-morphism $u_K \colon Z_K \to X_K$, and every point $\eta$ of $Z \times_{\operatorname{Spec} R} X$ lying over the closed point of $\operatorname{Spec} R$ and maximal among such points (any $y$ over the closed point with $\eta$ in the closure of $\{y\}$ equals $\eta$), there are an open $U \ni \eta$ of $Z \times_{\operatorname{Spec} R} X$ and an $R$-morphism $\tau \colon U \to X$ such that the induced morphism $U \to Z \times_{\operatorname{Spec} R} X$ with components $U \hookrightarrow Z \times_{\operatorname{Spec} R} X \to Z$ and $\tau$ is an open immersion, and on generic fibres the composite of $\tau_K$ with $e$ equals the restriction $U_K \to (Z \times_{\operatorname{Spec} R} X)_K$ followed by the $L_{X_K}$-product of the two $K$-points $u_K \circ (\mathrm{pr}_Z)_K$ and $e \circ (\mathrm{pr}_X)_K$ of $X_K$ over $(Z \times_{\operatorname{Spec} R} X)_K$; the second assertion is identical except that the two factors of the product are taken in the opposite order. Thus both left and right translation by $u_K$ extend, after an open modification, near every maximal point of the special fibre of $Z \times_{\operatorname{Spec} R} X$.
--
--   This is the passage from a weak Néron model to a single smooth separated model of finite type on which translations extend near maximal points of special fibres, in the form used for the construction of Néron models following Bosch–Lütkebohmert–Raynaud; it is the commutative edition, with commutativity of the group law as an extra hypothesis and both translation clauses retained. It is used in the construction of a Néron model with a relative group law over a Henselian discrete valuation ring, which in the Fermat application is applied to the Jacobian of a curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK),
      Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      (∃ x : X, f.base x = IsLocalRing.closedPoint R) ∧ IsIso e.1 ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1) := by sorry
