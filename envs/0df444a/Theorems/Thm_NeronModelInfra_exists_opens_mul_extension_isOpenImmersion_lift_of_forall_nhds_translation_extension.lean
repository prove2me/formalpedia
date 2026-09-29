-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
-- name    : NeronModelInfra.exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3a32e6ca-7d67-5f0d-b1b8-e8f89bba53a5
-- title:
--   Generic fibre group law extends to R-birational group law
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), $K$ a field that is its fraction field, $g_K\colon X_K\to\operatorname{Spec}K$ a scheme over $K$ and $L_{X_K}$ a `RelativeGroupLaw` for $g_K$, i.e. a functorial multiplication, unit and inverse on the sets of $K$-morphisms $T\to X_K$ over $\operatorname{Spec}K$, satisfying associativity, the unit laws, left inverses and compatibility with base change $T'\to T$. Let $f\colon X\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, and let $e$ be a morphism over $\operatorname{Spec}K$ from the generic fibre $X\times_{\operatorname{Spec}R}\operatorname{Spec}K$ (the second projection of the pullback of $f$ along $\operatorname{Spec}$ of $R\to K$) to $X_K$ whose underlying morphism of schemes is an isomorphism. Call $\eta\in X\times_R X$ maximal in the special fibre if $\mathrm{pr}_1$ followed by $f$ sends $\eta$ to the closed point of $R$ and every $y$ with $\eta$ in the closure of $\{y\}$ lying over the closed point equals $\eta$. Assume that for each such $\eta$ there are an open $U\ni\eta$ and an $R$-morphism $\tau\colon U\to X$ with $(\mathrm{pr}_1|_U,\tau)\colon U\to X\times_R X$ an open immersion and, on generic fibres, $e\circ\tau=(e\circ\mathrm{pr}_1)\cdot(e\circ\mathrm{pr}_2)$ in $L_{X_K}$ after restriction along $U$ (hypothesis `hL`), and likewise with the opposite product $(e\circ\mathrm{pr}_2)\cdot(e\circ\mathrm{pr}_1)$ (hypothesis `hR`). Then there are an open $W\subseteq X\times_R X$ and an $R$-morphism $m\colon W\to X$ such that $W$ contains every point not over the closed point and every maximal point of the special fibre; on generic fibres $e\circ m=(e\circ\mathrm{pr}_1)\cdot(e\circ\mathrm{pr}_2)$; both $\Phi=(\mathrm{pr}_1|_W,m)$ and $\Psi=(m,\mathrm{pr}_2|_W)$ from $W$ to $X\times_R X$ are open immersions; and the images of $\Phi$ and of $\Psi$ contain every maximal point of the special fibre.
--
--   This is the passage from local extensions of the translations near the maximal points of the special fibre to an $R$-birational group law on a smooth separated model extending the group law of the generic fibre, in the sense used for Weil's construction of a group scheme from a birational group law (Bosch–Lütkebohmert–Raynaud 4.3, 5.1). It is used in the construction of the relative group law on the Néron model, in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) := by sorry
