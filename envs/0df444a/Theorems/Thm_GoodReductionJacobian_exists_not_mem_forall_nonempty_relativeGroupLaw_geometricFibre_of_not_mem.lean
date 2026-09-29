-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
-- name    : GoodReductionJacobian.exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/cf8327bf-ad37-553a-aa32-18be758767da
-- title:
--   Spreading a relative group law to a basic open neighbourhood
-- statement:
--   Let $S$ be a Noetherian commutative ring, $Z$ a scheme and $f : Z \to \operatorname{Spec} S$ a morphism which is smooth and proper, and suppose $f$ admits a projective embedding over $S$: for some $N$ there is a closed immersion $\iota$ of $Z$ into $\operatorname{Proj}$ of the graded ring of homogeneous components of $S[x_0,\dots,x_N]$ with $\iota$ followed by the structure morphism `ProjSpace.π S N` equal to $f$. Assume every geometric fibre is connected: for each algebraically closed field $k$ and each ring homomorphism $x : S \to k$, the underlying space of $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$ is connected. Let $\varepsilon$ be a section of $f$, i.e. a morphism $\operatorname{Spec} S \to Z$ composing with $f$ to the identity, and let $s$ be a point of $\operatorname{Spec} S$, with associated prime $\mathfrak p_s$, such that for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ with $\ker x = \mathfrak p_s$ the projection $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k \to \operatorname{Spec} k$ carries a relative group law, that is, functorial multiplication, unit and inverse operations on $T$-points over $\operatorname{Spec} k$ satisfying associativity, the two unit laws, left inversion, and compatibility of multiplication with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Then there exists $r \in S$ with $r \notin \mathfrak p_s$ such that for every point $s'$ of $\operatorname{Spec} S$ with $r \notin \mathfrak p_{s'}$, every such geometric fibre over $s'$ again admits a relative group law.
--
--   This is the local form of the openness of the locus of points of the base whose geometric fibres carry a group law with unit $\varepsilon$: membership of the locus propagates to a basic open set $D(r)$. It is used to prove that this locus is open in $\operatorname{Spec} S$ for Noetherian $S$, a step in producing the abelian scheme structure on a Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.lean

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

theorem GoodReductionJacobian.exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (s : ↥(Spec (CommRingCat.of S)))
    (hs : (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x)))))) :
    ∃ r : S, r ∉ s.asIdeal ∧ ∀ s' : ↥(Spec (CommRingCat.of S)), r ∉ s'.asIdeal →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s'.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) := by sorry
