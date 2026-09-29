-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_isSymmetric_of_pullback_residue_iso_unit_of_isUnit_two_of_isArtinianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_isSymmetric_of_pullback_residue_iso_unit_of_isUnit_two_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/24c59876-e491-59c5-94ee-4af181077707
-- title:
--   Symmetric invertible sheaf trivial on closed fibre, Artin local base
-- statement:
--   Let $S$ be an Artinian local ring in which $2$ is invertible, let $A$ be a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$ over $S$, that is: for every scheme $T$ over $\operatorname{Spec} S$ with structure morphism $t$, a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi$ followed by $f$ equals $t\}$, satisfying associativity, the two unit laws and the left inverse law, with multiplication natural in $T$. Assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, for each point $s$ of $\operatorname{Spec} S$ the fibre $f^{-1}(s)$ of the underlying map of spaces is connected, and $f$ admits some relative group law. Let $N$ be a module on $A$ that is invertible, i.e. each point of $A$ has an open neighbourhood $U$ over which the restriction of $N$ is isomorphic to the unit module of $U$. Assume $N$ is symmetric for $L$ in the sense that, writing $[-1]$ for the morphism $A \to A$ underlying the $L$-inverse of the identity point of $f$, every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that $[-1]^{*}N$ and $N$ become isomorphic after restriction to $f^{-1}(U)$. Assume finally that the pullback of $N$ along the first projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} k \to A$, where $k$ is the residue field of $S$, is isomorphic to the monoidal unit. Then there exists an isomorphism of $N$ with the monoidal unit, i.e. $N$ is trivial on $A$.
--
--   This is the Artinian-base triviality criterion for symmetric invertible sheaves on an abelian scheme: triviality on the closed fibre propagates to the whole of $A$ when $2$ is invertible on the base. It is used in the study of canonical polarisations on fake elliptic curves, where it feeds the statement [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two), and it is obtained from the corresponding statement for small (square-zero, maximal-ideal-killed) thickenings together with the stability of symmetry under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_isSymmetric_of_pullback_residue_iso_unit_of_isUnit_two_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_isSymmetric_of_pullback_residue_iso_unit_of_isUnit_two_of_isArtinianRing
    {S : Type} [CommRing S] [IsLocalRing S] [IsArtinianRing S] (h2 : IsUnit (2 : S))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hsym : IsSymmetric f L N)
    (h0 : Nonempty ((Scheme.Modules.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))).obj N ≅ 𝟙_ _)) :
    Nonempty (N ≅ 𝟙_ _) := by sorry
