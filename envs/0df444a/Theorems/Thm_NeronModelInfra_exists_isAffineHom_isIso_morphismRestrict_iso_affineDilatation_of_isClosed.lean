-- Prove2me | Theorems.Thm_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
-- name    : NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/6038b442-1859-5074-a036-b28e0c2e37be
-- title:
--   Dilatation of a closed subset of the special fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain, so with a principal maximal ideal and a closed point `IsLocalRing.closedPoint R` of $\operatorname{Spec} R$), let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism locally of finite type, and let $Y$ be a closed subset of the underlying space of $X$ all of whose points are sent by $f$ to the closed point. Then there exist a scheme $D$ and a morphism $p : D \to X$ with the following four properties. First, $p$ is affine and locally of finite type. Second, for every open $W \subseteq X$ no point of which is sent by $f$ to the closed point, the restricted morphism $p \mid_W : p^{-1}(W) \to W$ is an isomorphism. Third, every point $d$ of $D$ with $f(p(d))$ the closed point satisfies $p(d) \in Y$. Fourth, for every affine open $U \subseteq X$, writing $A = \Gamma(X, U)$, and every $\pi \in R$ generating the maximal ideal of $R$, put $I =$ `PrimeSpectrum.vanishingIdeal` of the set of primes `hU.primeIdealOf y` for those $y \in U$ lying in $Y$, and let $a \in A$ be the restriction to $U$ of the global section $f^{\sharp}(\pi)$ obtained from $\pi$ through `Scheme.ΓSpecIso` and `f.appTop`; then there is an isomorphism of schemes $e$ from the open subscheme $p^{-1}(U)$ of $D$ onto $\operatorname{Spec}$ of [`AffineDilatation.Ring I a`](def/RingTheory_AffineDilatation.html#L20), that is, of the $A$-subalgebra `Algebra.adjoin A (gen I a)` of `Localization.Away a`, such that the open immersion $p^{-1}(U) \hookrightarrow D$ followed by $p$ coincides with $e$ followed by `Spec.map` of the algebra structure map $A \to$ [`AffineDilatation.Ring I a`](def/RingTheory_AffineDilatation.html#L20) followed by `hU.fromSpec`. The assertion is purely existential: no universal property of $(D, p)$ is claimed.
--
--   This is the existence of the dilatation (Néron blow-up) of a closed subset $Y$ of the special fibre of a scheme locally of finite type over a discrete valuation ring, in the form of Bosch–Lütkebohmert–Raynaud §3.2: an affine modification of $X$, unchanged away from the special fibre, whose affine charts are the affine dilatation algebras $A[I/\pi]$. It is used by the version indexed by an antitone family of closed subsets, from which iterated dilatations are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.lean

import Mathlib
import Definitions.Def_RingTheory_AffineDilatation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (Y : Set X) (hY : IsClosed Y) (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R) :
    ∃ (D : Scheme.{u}) (p : D ⟶ X),
      IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)) ∧
      (∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Y) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R),
        IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))))),
          (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec) := by sorry
