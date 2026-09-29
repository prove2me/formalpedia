-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre_of_isNoetherianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/48bf9c1c-8586-59dd-928c-20ec93903c0e
-- title:
--   Openness of the relative group law locus over a Noetherian base
-- statement:
--   Let $S$ be a Noetherian commutative ring, let $Z$ be a scheme and let $f : Z \to \operatorname{Spec} S$ be a morphism which is smooth and proper, and which is projective in the sense that there are an $N$ and a closed immersion $\iota$ of $Z$ into $\operatorname{Proj}$ of the graded ring of homogeneous components of $S[x_0,\dots,x_N]$ such that $\iota$ followed by the structural morphism `ProjSpace.π S N` equals $f$. Assume the geometric fibres are connected: for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$, the pullback of $f$ along $\operatorname{Spec}(x)$ has connected underlying space. Finally let $\varepsilon$ be a section of $f$, that is, a morphism $\operatorname{Spec} S \to Z$ whose composite with $f$ is the identity. Then the set of primes $s \subset S$ with the following property is open in $\operatorname{Spec} S$: for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ with $\ker x = s$, the base change $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k \to \operatorname{Spec} k$ admits a `RelativeGroupLaw` over $k$, i.e. an assignment to each $k$-scheme $T$ of a multiplication, unit and inverse on the set of $T$-points of the fibre over $\operatorname{Spec} k$, satisfying associativity, the two unit laws and left inversion, with the multiplication compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$.
--
--   This is the openness half of the statement that, for a smooth proper family with a section and connected geometric fibres over a Noetherian base, the locus where the geometric fibres carry a group law is open; it is the Noetherian-base form of the assertion used to cut out the abelian locus of such a family, and it feeds the version of the result stated without the Noetherian hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre_of_isNoetherianRing.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre_of_isNoetherianRing
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} := by sorry
