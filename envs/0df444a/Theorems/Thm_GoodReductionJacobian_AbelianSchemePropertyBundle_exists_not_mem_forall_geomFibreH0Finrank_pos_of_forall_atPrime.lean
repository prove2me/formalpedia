-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_geomFibreH0Finrank_pos_of_forall_atPrime
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_geomFibreH0Finrank_pos_of_forall_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/6cb01e30-e35f-5dc1-aca5-22a0c4319be8
-- title:
--   Positivity of geometric h⁰ spreads to a basic open set
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme, and $f\colon A\to\operatorname{Spec}S$ a morphism, equipped with a relative group law $L$ (a functorial group structure, natural in the base, on the sets of sections $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ for all $t\colon T\to\operatorname{Spec}S$) and with the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, every fibre of the underlying map of $f$ over a point of $\operatorname{Spec}S$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module over $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module sheaf, and assume `KernelIsTwoTorsion`: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}S$ and every section $x$ of $f$ over $t$, the pullback along the slice of $x$ of the Mumford bundle $m^{*}\mathcal L\otimes p_1^{*}\mathcal L^{\vee}\otimes p_2^{*}\mathcal L^{\vee}$ is, locally on the base $\operatorname{Spec}R$, isomorphic to the unit object exactly when $x+x$ is the identity section. Let $\mathfrak p$ be a prime of $S$, and suppose that for every algebraically closed field $k$ and every ring homomorphism $sk\colon S\to k$ sending every element outside $\mathfrak p$ to a non-zero element, the geometric fibre invariant $\operatorname{geomFibreH0Finrank} f\,\mathcal L\,k\,sk$ — the $k$-dimension of the global sections of the pullback of $\mathcal L$ to $A\times_{\operatorname{Spec}S}\operatorname{Spec}k$ — is positive. Then there is $g\in S$ with $g\notin\mathfrak p$ such that this dimension is positive for every algebraically closed field $k$ and every $sk\colon S\to k$ with $sk(g)\neq 0$.
--
--   This is a spreading-out statement for positivity of $h^0$ of a line bundle on an abelian scheme whose theta group kernel is exactly the $2$-torsion: positivity at all geometric points lying over generalisations of $\mathfrak p$ propagates to all geometric points over a basic open neighbourhood $D(g)$ of $\mathfrak p$. It is used in the construction of canonical polarisation data on fake elliptic curves, where the positivity clause must be made to hold on a neighbourhood of a prime rather than only at that prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_geomFibreH0Finrank_pos_of_forall_atPrime.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_geomFibreH0Finrank_pos_of_forall_atPrime
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛)
    (𝔭 : PrimeSpectrum S)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      (∀ s : S, s ∉ 𝔭.asIdeal → sk s ≠ 0) → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), sk g ≠ 0 → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk := by sorry
