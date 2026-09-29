-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ebff6469-1293-535b-a1cf-566a829fe05e
-- title:
--   Clopenness of the locus where given n-torsion sections span
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$: a family of group structures on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $\varphi : T \to A$ with $\varphi \circ t^{-1}$-compatibility $\varphi$ followed by $f$ equal to $t$, given by operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ satisfying the group axioms and with $\mathrm{mul}$ compatible with precomposition along any $\psi : T' \to T$ over $\operatorname{Spec} S$. Assume $L$ is commutative, and that $f$ satisfies the bundle of properties $\mathrm{AbelianSchemePropertyBundle}$: $f$ is smooth and proper, every fibre of the underlying map of $f$ is connected, and $f$ admits a relative group law. Let $g, n$ be natural numbers with the image of $n$ in $S$ a unit, and let $P_0,\dots,P_{2g-1}$ be sections of $f$ over $\operatorname{Spec} S$ (sections over the identity) each killed by $n$, where $n \cdot P$ means the $n$-fold $L$-product of $P$ with itself. Then the following subset of the topological space $\operatorname{Spec} S$ is open and closed: the set of primes $s$ such that for every algebraically closed field $k$ and every ring homomorphism $s_k : S \to k$ whose kernel is the prime ideal $s$, every point $Q$ of $A$ over $\operatorname{Spec}$ of $s_k$ killed by $n$ is of the form $\sum_i c_i P_i$ for some coefficients $c_i \in \{0,\dots,n-1\}$, the combination being the $L$-product of the $c_i$-th powers of the base changes of the $P_i$ along that geometric point.
--
--   This is the statement that the locus in the base over which a prescribed family of $2g$ global $n$-torsion sections generates the full $n$-torsion of every geometric fibre is open and closed, when $n$ is invertible; it is the generation (spanning) half of the conditions defining a full level-$n$ structure on an abelian scheme. It feeds the combined clopenness statement [`GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists), in which spanning is coupled with injectivity of the coefficient map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra hiding schemeHomOverComp
open GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q} := by sorry
