-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_ideal_nsmul_eq_one_iff_le_ker
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_ideal_nsmul_eq_one_iff_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/42d3d0e7-c0b7-554d-aa79-5177c0ecede5
-- title:
--   Torsion condition on a section cut out by an ideal
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism. Let $L$ be a relative group law for $f$ in the sense of the project's structure `RelativeGroupLaw`: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} S$ it provides a multiplication, a unit and an inversion on the set of $t$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, subject to associativity, the two unit laws, left inverses, and naturality of the multiplication under precomposition with any $\psi : T' \to T$ over the base. Let $hA$ assert the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth, proper, has connected fibres over every point of $\operatorname{Spec} S$, and admits some relative group law; of these only properness enters the proof. Let $n$ be a natural number and $P$ a section of $f$, i.e. a morphism $\operatorname{Spec} S \to A$ whose composite with $f$ is the identity. The conclusion is that there is an ideal $I \subseteq S$ such that for every commutative ring $S'$ and every ring homomorphism $\varphi : S \to S'$, the $n$-fold $L$-sum (defined by recursion, with empty sum the unit) of the point $\operatorname{Spec}\varphi$ followed by $P$, taken over $t = \operatorname{Spec}\varphi : \operatorname{Spec} S' \to \operatorname{Spec} S$, equals the unit point $L.\mathrm{one}$ over that $t$ if and only if $I \subseteq \ker \varphi$.
--
--   This is the statement that the condition '$P$ is $n$-torsion' on a section of an abelian scheme over an affine base is a closed condition, represented by the closed subscheme $V(I)$ of $\operatorname{Spec} S$; classically it follows from separatedness of $f$, the locus being the preimage of the diagonal under $(nP, e)$. It is used in the construction of fine moduli and projective embedding results for framed polarised abelian schemes, where it cuts out the requirement that a tuple of marked sections be $n$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_ideal_nsmul_eq_one_iff_le_ker.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.exists_ideal_nsmul_eq_one_iff_le_ker
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (n : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    ∃ I : Ideal S, ∀ (S' : Type) [CommRing S'] (φ : S →+* S'),
      L.nsmul (Spec.map (CommRingCat.ofHom φ)) n
          (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _) P) =
        L.one (Spec.map (CommRingCat.ofHom φ)) ↔ I ≤ RingHom.ker φ := by sorry
