-- Prove2me | Theorems.Thm_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
-- name    : NeronModelInfra.exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/7f0f8554-b88c-5c41-904f-728f34204682
-- title:
--   Extending an endomorphism of G_ℚ over mathbb Z₍ₚ₎
-- statement:
--   Let $p$ be a prime and let $R$ be a discrete valuation domain with $\mathbb Q$ as its fraction field which is the localisation of $\mathbb Z$ at the prime ideal $(p)$. Let $g\colon G\to\operatorname{Spec}\mathbb Z$ be smooth, separated and quasi-compact and let $L$ be a relative group law on $g$, i.e. a group structure on each set of $\operatorname{Spec}\mathbb Z$-morphisms $T\to G$ over a given $t\colon T\to\operatorname{Spec}\mathbb Z$ (multiplication, unit, inverse, associativity, unit laws, left inverse), natural under precomposition with morphisms $\psi$ over $\operatorname{Spec}\mathbb Z$. Write $G_R$ for the pullback of $g$ along $\operatorname{Spec}R\to\operatorname{Spec}\mathbb Z$. Let $\eta\in G_R$ lie over the closed point of $R$ and specialise to every point of $G_R$ over the closed point. Let $\varphi_\eta$ be a pair consisting of an endomorphism of $G_{\mathbb Q}$ commuting with the projection to $\operatorname{Spec}\mathbb Q$, let $\varphi_K$ be an endomorphism of the pullback of $G_R\to\operatorname{Spec}R$ along $\operatorname{Spec}\mathbb Q\to\operatorname{Spec}R$, and let $\theta$ be a morphism from the latter to $G_{\mathbb Q}$ compatible with both projections, with $\theta\circ\varphi_K=\varphi_\eta\circ\theta$. Let $V\subseteq G_R$ be open containing $\eta$ and every point not over the closed point, and $v\colon V\to G_R$ a morphism over $\operatorname{Spec}R$ whose restriction along the first projection (whose image lies in $V$) agrees with $\varphi_K$ followed by that projection. Then there is $g_A\colon G_R\to G$ with $g\circ g_A$ equal to $g$ composed with the first projection, such that every $j\colon G\times_{\mathbb Z}\operatorname{Spec}\mathbb Q\to G_R$ commuting with the projections to $G$ satisfies $g_A\circ j=\operatorname{pr}_1\circ\varphi_\eta$.
--
--   This is the form of Weil's extension theorem for smooth separated group schemes over a discrete valuation ring needed in the construction of Hecke correspondences: a morphism defined on an open containing the generic fibre and the generic point of the closed fibre extends over the whole of $G_R$, compatibly with the given endomorphism of the generic fibre. It supplies the per-prime extension clause used by [`ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic`](thm.html#ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem NeronModelInfra.exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw ℤ g)
    (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
    (hη : (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R → η ⤳ x)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
    (hθ₁ : θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫
        pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hθ₂ : θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφ : φK ≫ θ = θ ≫ φη.1)
    (V : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).Opens)
    (v : (V : Scheme.{0}) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hv : v ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
      V.ι ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hVη : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hηV : η ∈ V)
    (hle : Set.range (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))).base ⊆ Set.range V.ι.base)
    (hlift : IsOpenImmersion.lift V.ι
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) hle ≫ v =
      φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) :
    ∃ gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ⟶ G,
      gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ≫ g ∧
      ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
          pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))),
        j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
          pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by sorry
