-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/48f182f7-76f8-5477-8bd5-8d3f8f02484e
-- title:
--   Relative group law over the local ring at s
-- statement:
--   Let $R$ be a noetherian commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism that is smooth and proper; suppose $f$ is projective in the explicit sense that for some $N$ there is a closed immersion $\iota : A \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$ with $\iota$ followed by the structure morphism `ProjSpace.π R N` equal to $f$. Let $e$ be a section of $f$, i.e. a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is the identity, and let $W \subseteq \operatorname{Spec} R$ be a clopen subset such that (i) for every $s \in W$ the fibre $f^{-1}(s)$, as a subset of the space of $A$, is connected and nonempty, and (ii) for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} R$ whose image lies in $W$, the base change $A \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ is smooth and proper, has connected nonempty fibres, and admits a relative group law. Then for every $s \in W$, writing $R_{\mathfrak p}$ for the localisation of $R$ at the prime $\mathfrak p$ corresponding to $s$, the base change $A \times_{\operatorname{Spec} R} \operatorname{Spec} R_{\mathfrak p} \to \operatorname{Spec} R_{\mathfrak p}$ carries a relative group law $L$ — a functorial group structure on $T$-points over $\operatorname{Spec} R_{\mathfrak p}$, compatible with base change in $T$ — whose unit section over $T = \operatorname{Spec} R_{\mathfrak p}$ with $t$ the identity is the base change of $e$, namely the morphism into the fibre product determined by $\operatorname{Spec}(R \to R_{\mathfrak p})$ followed by $e$ and by the identity.
--
--   This is the local step in equipping a smooth proper family with connected geometric fibres that are abelian varieties over the clopen locus $W$ with a group law whose unit is a prescribed section, the base being the local ring at a point of $W$. It is used by the corresponding statement over a basic open neighbourhood $D(r) \ni s$, obtained from it by spreading the group law out from $R_{\mathfrak p}$ to a localisation $R[1/r]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (s : Spec (CommRingCat.of R)) (hsW : s ∈ W) :
    ∃ L : RelativeGroupLaw (Localization.AtPrime s.asIdeal)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime s.asIdeal))))),
      (L.one (𝟙 _)).1 =
        pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime s.asIdeal))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by sorry
