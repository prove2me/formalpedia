-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_schemeKer_of_locallyQuasiFinite
-- name    : GoodReductionJacobian.RelativeGroupLaw.isAffine_schemeKer_of_locallyQuasiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e80713b9-dca5-5687-9432-9114b89ec0ea
-- title:
--   Quasi-finite n-torsion kernels are affine over one-dimensional bases
-- statement:
--   Let $R$ be a commutative Noetherian ring whose Krull dimension satisfies $\operatorname{ringKrullDim} R \le 1$, let $A$ be a scheme and $f\colon A \to \operatorname{Spec} R$ a separated morphism locally of finite type. Let $G$ be a relative group law for $f$, that is, a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse and naturality in $T$) on the sets $\{\varphi\colon T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over each $t\colon T \to \operatorname{Spec} R$. Fix $n \in \mathbb{N}$, and form the endomorphism `G.schemeNsmul n` of $A$, the underlying morphism of the $n$-th multiple, in this group structure, of the identity point of $A$ over $f$. Let $G.\mathtt{schemeKer}\ n$ be the pullback of `G.schemeNsmul n` along the underlying morphism of the unit point $G.\mathrm{one}(\mathbb{1}_{\operatorname{Spec} R})$, with structure morphism $G.\mathtt{schemeKerStr}\ n$ the second projection to $\operatorname{Spec} R$. If this structure morphism is locally quasi-finite and quasi-compact, then $G.\mathtt{schemeKer}\ n$ is an affine scheme.
--
--   This is the group-scheme-theoretic form of affineness of $n$-torsion: over a Noetherian base of dimension at most one, the kernel of multiplication by $n$ on a separated group scheme locally of finite type is affine as soon as it is quasi-finite and quasi-compact over the base, so it need not be finite (the interesting case being primes of bad reduction, where the torsion of a Néron model is quasi-finite only). It is used in the construction of torsion data attached to the Néron model of $J_0(p)$ and its identity component, where affineness of the kernel is what allows the torsion to be described by a ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_schemeKer_of_locallyQuasiFinite.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem GoodReductionJacobian.RelativeGroupLaw.isAffine_schemeKer_of_locallyQuasiFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f) (n : ℕ) [LocallyQuasiFinite (G.schemeKerStr n)] [QuasiCompact (G.schemeKerStr n)] :
    IsAffine (G.schemeKer n) := by sorry
