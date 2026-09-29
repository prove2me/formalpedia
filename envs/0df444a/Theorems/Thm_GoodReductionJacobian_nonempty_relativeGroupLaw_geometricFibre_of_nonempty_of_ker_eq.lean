-- Prove2me | Theorems.Thm_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
-- name    : GoodReductionJacobian.nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/734ee2ec-e4c7-5ee9-aceb-284c9a0e46ac
-- title:
--   Group law on a geometric fibre is independent of the geometric point
-- statement:
--   Let $S$ be a commutative ring, $Z$ a scheme and $f : Z \to \operatorname{Spec} S$ a morphism which is assumed to factor as a closed immersion $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $S$, for some $N$, followed by the structure morphism `ProjSpace.π S N` to $\operatorname{Spec} S$; that is, $Z$ is presented as a closed subscheme of $\mathbb{P}^N_S$ over $S$. Let $s$ be a point of $\operatorname{Spec} S$, and let $x : S \to k$ and $x' : S \to k'$ be ring homomorphisms into algebraically closed fields $k$, $k'$ whose kernels both equal the prime ideal of $s$, i.e. two geometric points of $\operatorname{Spec} S$ lying over $s$. Assume that the geometric fibre $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$, with its second projection to $\operatorname{Spec} k$, admits a relative group law over $k$: a rule assigning to every scheme $T$ and every morphism $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi : T \to Z_k \mid \varphi$ followed by the projection equals $t\}$, satisfying associativity, the two unit laws and the left inverse law, and such that the multiplication is compatible with precomposition along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. The conclusion is that the geometric fibre $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k'$ over $\operatorname{Spec} k'$ likewise admits such a relative group law.
--
--   This is the statement that whether a geometric fibre of a projective $S$-scheme carries a group law depends only on the underlying point $s$ of $\operatorname{Spec} S$, not on the choice of algebraically closed field through which the geometric point is taken; by symmetry in $k$ and $k'$ it yields the corresponding equivalence. It is used in showing that the locus of points of $\operatorname{Spec} S$ whose geometric fibres admit a group law is open, and in the criterion comparing smoothness and irreducibility of geometric fibres for two geometric points with the same kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.nonempty_relativeGroupLaw_geometricFibre_of_nonempty_of_ker_eq
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (s : ↥(Spec (CommRingCat.of S)))
    (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k) (hx : RingHom.ker x = s.asIdeal)
    (k' : Type u) [Field k'] [IsAlgClosed k'] (x' : S →+* k') (hx' : RingHom.ker x' = s.asIdeal)
    (h : Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) :
    Nonempty (RelativeGroupLaw k' (pullback.snd f (Spec.map (CommRingCat.ofHom x')))) := by sorry
