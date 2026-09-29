-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_not_mem_and_abelian_geometricFibre
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_not_mem_and_abelian_geometricFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/4225fd93-4a58-5f51-a1ec-3eb63945c138
-- title:
--   Openness of the abelian geometric-fibre locus over a basic open
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme, and $f : Z \to \operatorname{Spec} R$ a morphism that is proper, flat and locally of finite presentation. Assume $f$ is projective in the following explicit sense (`hproj`): there are $N \in \mathbb{N}$ and a closed immersion $\iota$ of $Z$ into $\operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$ such that $\iota$ followed by the structure morphism $\pi$ of $\mathbb{P}^N_R$ equals $f$. Fix $g \in \mathbb{N}$, a section $\varepsilon$ of $f$ (an element of $\{\varphi : \operatorname{Spec} R \to Z \mid \varphi \text{ followed by } f = \mathrm{id}\}$), and $r \in R$ such that for every prime $s$ of $R$ with $r \notin s$, every algebraically closed field $k$ and every ring homomorphism $x : R \to k$ with kernel $s$, the second projection of the pullback of $f$ along $\operatorname{Spec}$ of $x$ is smooth, the pullback scheme is irreducible and its topological Krull dimension equals $g$. The conclusion is that the set of primes $s$ with $r \notin s$ such that, for all such $k$ and $x$, the geometric fibre is smooth, irreducible, of topological Krull dimension $g$, and moreover admits a `RelativeGroupLaw` over $k$ — a functorial group structure on the sets of $T$-points of the fibre over $k$-schemes $T$, with multiplication, unit, inverse satisfying associativity, the unit laws, left inversion, and naturality of multiplication in $T$ — is open in $\operatorname{Spec} R$.
--
--   This is the openness step in the construction of the locus of the base over which a projective flat family acquires abelian-scheme fibres: on the basic open set $D(r)$, where smoothness, irreducibility and fibre dimension $g$ are already assumed, the additional requirement that the geometric fibres carry a group law cuts out an open subset. It is used in the comparison of such loci under base change, [`GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback), on the way to the good-reduction properties of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_not_mem_and_abelian_geometricFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_not_mem_and_abelian_geometricFibre
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (r : R)
    (hr : ∀ s : ↥(Spec (CommRingCat.of R)), r ∉ s.asIdeal → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g) :
    IsOpen {s : ↥(Spec (CommRingCat.of R)) | r ∉ s.asIdeal ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} := by sorry
