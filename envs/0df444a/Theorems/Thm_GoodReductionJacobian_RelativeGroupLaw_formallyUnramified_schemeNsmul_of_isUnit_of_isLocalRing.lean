-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/74a7be79-e0f8-54f4-bfb0-1a9981314ada
-- title:
--   Multiplication by a unit is formally unramified
-- statement:
--   Let $R$ be a commutative local ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ be a morphism, and let $G$ be a relative group law on $f$ over $R$: for every scheme $T$ and every structure morphism $t : T \to \operatorname{Spec} R$, a multiplication, a neutral element and an inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi$ followed by $f$ equals $t\}$, satisfying associativity, the two unit laws and left inverses, and with multiplication natural in $T$ in the sense that precomposition with $\psi : T' \to T$ over $\operatorname{Spec} R$ commutes with the multiplications. Assume in addition that the multiplication of $G$ is commutative on the points over every base $t$, and let $n$ be a natural number whose image in $R$ is a unit. Then the morphism $A \to A$ obtained as the first component of the $n$-fold power of the tautological $A$-point $\mathrm{id}_A$ (the power being defined by recursion: the neutral element for $n = 0$, and multiplication of the $(n-1)$-st power by the point for successors) is formally unramified in the sense of Mathlib's `FormallyUnramified`.
--
--   This is the statement that multiplication by $n$ on a commutative group object over a base in which $n$ is invertible is formally unramified, the functorial shadow of the vanishing of $\Omega$ for $[n]$ on a commutative group scheme. It feeds the degree computation for $[n]$, the rigidity statements for torsion points used in the Néron model material, and the corresponding statements for fake elliptic curves; the proof reduces it to the criterion `formallyUnramified_schemeNsmul_of_forall_sqZero`, which asks that an $n$-torsion point over an affine base reducing to the unit modulo a square-zero ideal be the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) := by sorry
