-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0dbbfca6-015e-518e-9713-556d0d7d43c8
-- title:
--   Multiplication by n on an abelian scheme is finite flat
-- statement:
--   Let $B$ be a Noetherian commutative ring, let $A$ be a scheme, let $f : A \to \operatorname{Spec} B$ be a morphism, and let $L$ be a relative group law for $f$ over $B$: for every scheme $T$ and every $t : T \to \operatorname{Spec} B$ a multiplication, unit and inverse on the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the unit laws and left inverse, and compatible with precomposition in $T$. Assume $L$ is commutative, i.e. its multiplication on each such set of $t$-points is commutative, and that `AbelianSchemePropertyBundle B f` holds: $f$ is smooth and proper, each fibre $f^{-1}(s)$ of the underlying map on points is connected, and $f$ admits some relative group law. Assume further that $f$ is smooth of relative dimension $g$, and let $n \neq 0$. Write $[n] =$ `L.schemeNsmul n` $: A \to A$ for the underlying morphism of the $n$-fold $L$-sum of the identity point $\mathbb{1}_A$, and let `L.schemeKerStr n` be the projection to $\operatorname{Spec} B$ from the pullback of $[n]$ along the unit section $\operatorname{Spec} B \to A$ of $L$. Then `L.schemeKerStr n` is finite, flat and locally of finite presentation, and its rank at every point $s$ of $\operatorname{Spec} B$ equals $n^{2g}$; moreover $[n]$ is finite, flat, locally of finite presentation and surjective.
--
--   This is the standard statement that on an abelian scheme of relative dimension $g$ multiplication by $n \neq 0$ is a finite flat surjection and the $n$-torsion subscheme $A[n]$ is finite locally free of constant rank $n^{2g}$ over the base. It is the input for torsion level structures and for the formal-group and lifting arguments that use the degree of $[n]$, and is cited by the existence of unique lifts of homomorphisms along infinitesimal thickenings, by the comparison of an abelian scheme over a local base with the functor of admissible classes, and by the kernel computations for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_schemeKerStr_and_schemeNsmul_of_abelianSchemePropertyBundle
    {B : Type} [CommRing B] [IsNoetherianRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle B f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) ∧ LocallyOfFinitePresentation (L.schemeKerStr n) ∧
      (∀ s : ↥(Spec (CommRingCat.of B)), (L.schemeKerStr n).finrank s = n ^ (2 * g)) ∧
      IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) ∧ LocallyOfFinitePresentation (L.schemeNsmul n) ∧
      Surjective (L.schemeNsmul n) := by sorry
