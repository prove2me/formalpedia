-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal_of_smooth
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e8f432dc-764b-56d8-b0c8-e3b1bbbccd99
-- title:
--   Kernel of reduction modulo J^{μ+1}=0 is killed by N^μ
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law for $f$ over $B$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over a given $t : T \to \operatorname{Spec} B$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inversion, and with multiplication compatible with precomposition along any $\psi : T' \to T$ over $\operatorname{Spec} B$. Assume $L$ is commutative, i.e. its multiplication on each such set of points is commutative, and that $f$ is smooth. Let $B'$ be a $B$-algebra, $N$ a natural number whose image in $B'$ is $0$, $J \subseteq B'$ an ideal and $\mu$ a natural number with $J^{\mu+1} = 0$, and let $P$ be a $B'$-point of $A$ over $B$, i.e. a morphism $\operatorname{Spec} B' \to A$ whose composite with $f$ is $\operatorname{Spec}$ of the structure map $B \to B'$. Assume $P$ lies in the kernel of reduction modulo $J$: the morphism $\operatorname{Spec}(B'/J) \to \operatorname{Spec} B'$ induced by the quotient map, followed by $P$, equals the unit section over $B'/J$. Then the $N^\mu$-fold iterate of $P$ under the group law, formed by $N^\mu$ successive multiplications by $P$ starting from the unit, is the unit section over $B'$.
--
--   This is the coordinate-free form of the rigidity lemma of Katz and Drinfeld for the kernel of reduction of a smooth commutative group scheme along a nilpotent ideal: only smoothness and commutativity of the group law are assumed, formal coordinates at the unit section being produced Zariski-locally on the base. It feeds the construction of homomorphisms compatible with multiplication by $N^\mu$ on points in the kernel of reduction, via [`GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal_of_smooth.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal_of_smooth
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (hc : L.IsCommutative) (hf : Smooth f)
    {B' : Type} [CommRing B'] [Algebra B B'] (N : ℕ) (hN : (N : B') = 0)
    (J : Ideal B') (μ : ℕ) (hJ : J ^ (μ + 1) = ⊥)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) (hP : L.IsInfinitesimal J P) :
    L.nsmul (Scheme.specOver (𝒪 := B) B') (N ^ μ) P = L.one (Scheme.specOver (𝒪 := B) B') := by sorry
