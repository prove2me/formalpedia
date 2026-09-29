-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_finComb_injective_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_forall_finComb_injective_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0a9ec1c7-18ae-5905-a3f4-7f972602cc58
-- title:
--   Clopen independence locus for n-torsion sections
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$: a rule assigning to each $t : T \to \operatorname{Spec} S$ a multiplication, unit and inverse on the set $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying the group axioms and compatible with precomposition in $T$. Assume $L$ is commutative, that $f$ satisfies the bundle of properties consisting of smoothness, properness, connectedness of each fibre of $f$ on underlying spaces, and existence of a relative group law; fix $g, n \in \mathbb{N}$ with the image of $n$ in $S$ a unit, and sections $P_i$ of $f$ over $\mathbf{1}_{\operatorname{Spec} S}$ for $i \in \mathrm{Fin}(2g)$ such that the $n$-fold iterate of the law on each $P_i$ is the unit section. Then the set of points $s$ of $\operatorname{Spec} S$ with the following property is open and closed: for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$ whose kernel is the prime ideal $s$, and all $c, c' : \mathrm{Fin}(2g) \to \mathrm{Fin}\ n$, equality of the products $\prod_i (P_i)^{c_i}$ and $\prod_i (P_i)^{c'_i}$, formed in the group of sections over $\operatorname{Spec} k \to \operatorname{Spec} S$ after base change of the $P_i$ along $\operatorname{Spec}(sk)$, forces $c = c'$.
--
--   This is the statement that the locus where $2g$ given $n$-torsion sections generate a free $(\mathbb{Z}/n)^{2g}$ on geometric fibres is open and closed when $n$ is invertible on the base, the independence clause in the level-structure data for polarised abelian schemes. It feeds the combined clopen statement [`GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists), where independence is coupled with existence of torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_finComb_injective_of_isUnit.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_forall_finComb_injective_of_isUnit
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      ∀ c c' : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
        c = c'} := by sorry
