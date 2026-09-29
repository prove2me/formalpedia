-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_relativeGroupLaw_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_relativeGroupLaw_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/2839e4a2-d637-5a04-b101-d4ca72cb3aab
-- title:
--   Stabiliser of an invertible sheaf as closed subgroup scheme
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} k$ is connected, and $f$ admits at least one relative group law; let $L$ be a relative group law for $f$ (a group structure, natural in the base, on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over $t : T \to \operatorname{Spec} k$), assumed commutative, and let $\mathcal L$ be an $\mathcal O_A$-module that is invertible in the sense that every point of $A$ has an open neighbourhood on which $\mathcal L$ restricts to a module isomorphic to the unit. Then there exist a scheme $K$, a closed immersion $\iota : K \to A$ and a relative group law $L_K$ for $\iota$ followed by $f$ such that: (i) for every $t : T \to \operatorname{Spec} k$ and all points $P, Q$ of $K$ over $t$, the composite of $L_K$-multiplication $L_K.\mathrm{mul}\,t\,P\,Q$ with $\iota$ equals $L.\mathrm{mul}$ applied to $P$ followed by $\iota$ and $Q$ followed by $\iota$, so $\iota$ is a homomorphism on points; and (ii) for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x : \operatorname{Spec} R \to A$ with $x \circ f = t$, the morphism $x$ factors through $\iota$ if and only if the pullback along `sliceAt f x` of the Mumford bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ on $A \times_k A$ is isomorphic to the unit module of $A \times_k \operatorname{Spec} R$ locally on the base, i.e. each point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage under $p_2$ the two modules become isomorphic.
--
--   This is the statement that the stabiliser $K(\mathcal L) \subseteq A$ of an invertible sheaf on an abelian variety over an algebraically closed field is a closed subgroup scheme, described by its functor of points on affine test schemes through triviality of the slices of the Mumford bundle. It strengthens the purely scheme-theoretic representability statement over a Noetherian base by adding the group law, and is used in the treatment of trivial kernels in characteristic zero and in the finiteness statement for stabilisers with non-zero Euler characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_relativeGroupLaw_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_relativeGroupLaw_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (K : Scheme.{0}) (ι : K ⟶ A) (_ : IsClosedImmersion ι) (LK : RelativeGroupLaw k (ι ≫ f)),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t (ι ≫ f)),
        (LK.mul t P Q).1 ≫ ι = (L.mul t ⟨P.1 ≫ ι, by rw [Category.assoc, P.2]⟩ ⟨Q.1 ≫ ι, by rw [Category.assoc, Q.2]⟩).1) ∧
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        (∃ κ : Spec (CommRingCat.of R) ⟶ K, κ ≫ ι = x.1) ↔
          LocIsoOnBase (pullback.snd f t)
            ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by sorry
