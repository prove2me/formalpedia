-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_forall_kernelIsTwoTorsion_geomFibre
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_forall_kernelIsTwoTorsion_geomFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/84e1c080-76d0-501c-8977-490ea8d79f1a
-- title:
--   Symmetric square roots with 2-torsion kernel are principal
-- statement:
--   Let $R$ be a noetherian commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}R$ a morphism, equipped with a relative group law $L$ (a functorial group structure on the sets $\{\varphi\colon T\to A : \varphi\circ f = t\}$ of $A$-points over arbitrary $t\colon T\to\operatorname{Spec}R$, with multiplication, unit, inverse, the group axioms and compatibility with base change along $T'\to T$), and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every set-theoretic fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathcal L$ and $M$ be modules on $A$, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction is isomorphic to the unit sheaf. Write $[-1]$ for the inversion morphism $A\to A$ coming from $L$ applied to the identity point. Two modules on $A$ are called isomorphic locally on the base when each point $s\in\operatorname{Spec}R$ has an open neighbourhood $U$ such that the restrictions to $f^{-1}(U)$ are isomorphic. Assume $M$ is symmetric, i.e. $[-1]^*M$ and $M$ are isomorphic locally on the base, and that $\mathcal L$ and $M\otimes[-1]^*M$ are isomorphic locally on the base. Assume further that for every algebraically closed field $k$ and every ring homomorphism $\varphi\colon R\to k$ the pulled-back bundle on the fibre $A\times_{\operatorname{Spec}R}\operatorname{Spec}k$ has kernel exactly the $2$-torsion for the base-changed group law: for every commutative ring $R'$, every $t\colon\operatorname{Spec}R'\to\operatorname{Spec}k$ and every point $x$ of the fibre over $t$, the pullback along the slice at $x$ of the Mumford bundle $m^*\mathcal L_k\otimes(p_1^*\mathcal L_k^\vee\otimes p_2^*\mathcal L_k^\vee)$ is isomorphic to the unit locally on the base if and only if $x\cdot x$ is the unit point. The conclusion is that $M$ has trivial kernel: for every commutative ring $R'$, every $t\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ and every point $x$ of $A$ over $t$, if the pullback along the slice at $x$ of the Mumford bundle of $M$ is isomorphic to the unit locally on the base, then $x$ is the unit point over $t$.
--
--   Classically: a symmetric square root of a line bundle whose Mumford kernel is exactly the $2$-torsion subscheme is principal, here in the relative form over a noetherian base with the hypothesis on the kernel imposed on all geometric fibres. It feeds the construction of principal polarisations on Jacobians, being used in the corresponding statement over a base that is finite at a prime and faithfully flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_forall_kernelIsTwoTorsion_geomFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_forall_kernelIsTwoTorsion_geomFibre
    {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 M : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hM : Scheme.Modules.IsInvertible M)
    (hsM : IsSymmetric f L M)
    (hrM : LocIsoOnBase f 𝓛 (M ⊗ (Scheme.Modules.pullback (negMor f L)).obj M))
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : R →+* k),
      KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (L.baseChange (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓛)) :
    KernelTrivial f L M := by sorry
