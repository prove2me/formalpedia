-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/8459c87c-0d62-532b-abc6-65eb7b2eb27a
-- title:
--   Unique commutative relative group law with prescribed unit section
-- statement:
--   Let $R$ be a noetherian commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism that is smooth ($hs$), proper ($hp$) and has topologically connected fibres: for every point $s$ of $\operatorname{Spec} R$ the set $f^{-1}(s)$ is connected and nonempty ($hc$). Assume $f$ is projective in the strict sense that for some $N$ there is a closed immersion $\iota$ of $A$ into $\operatorname{Proj}$ of the ring of homogeneous polynomials in $N+1$ variables over $R$ with $\iota$ followed by the structure morphism `ProjSpace.π R N` equal to $f$. Let $e$ be a section of $f$, i.e. a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is the identity. Assume further that for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} R$ the base change $\operatorname{pullback.snd} f\,s$ over $\operatorname{Spec} k$ satisfies `AbelianSchemePropertyBundle`: it is smooth, proper, has connected fibres, and its functor of points carries at least one relative group law. The conclusion asserts the existence of a `RelativeGroupLaw` $L$ for $f$ over $R$, that is: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, both unit laws and left inversion, with multiplication natural under precomposition by any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$; such that the unit at $t = \mathbf{1}_{\operatorname{Spec} R}$ is $e$, the law is commutative at every $T$ and $t$, and any relative group law for $f$ whose unit at the identity is $e$ coincides with $L$.
--
--   This is the construction of the abelian-scheme group law out of a section: a smooth projective morphism with connected fibres over a noetherian base whose geometric fibres are abelian varieties carries exactly one relative group law with a prescribed unit section, and that law is commutative (the scheme-theoretic form of the classical rigidity statements for abelian varieties). It feeds the representability results for framed polarised abelian schemes and the Jacobian-with-good-reduction interface further along the route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing.lean

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

theorem GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f) (hc : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      AbelianSchemePropertyBundle k (pullback.snd f s)) :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e ∧ L.IsCommutative ∧
      ∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e → L' = L := by sorry
