-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_finComb_injective_and_forall_torsion_exists
-- name    : GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/77ccca01-5fe0-5439-9a6b-4ec702a46a5d
-- title:
--   Full-level locus for n-torsion sections is clopen
-- statement:
--   Let $S$ be a commutative ring, let $f : A \to \operatorname{Spec} S$ be a morphism of schemes, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}(t, f)$ of sections of $f$ along an arbitrary $t : T \to \operatorname{Spec} S$ (unit, multiplication and inverse, associativity, unit and inverse laws, and compatibility with base change $\psi$ with $\psi \circ t' = t$, written diagrammatically). Assume $L$ is commutative, that $f$ satisfies the bundle `AbelianSchemePropertyBundle` — $f$ smooth and proper, all topological fibres $f^{-1}(s)$ connected, and a relative group law exists — and that for some $g : \mathbb{N}$ every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $n : \mathbb{N}$ have invertible image in $S$, and let $P : \mathrm{Fin}(2g) \to$ sections of $f$ over the identity of $\operatorname{Spec} S$ satisfy $n \cdot P_i = 1$ for the iterated multiplication `nsmul` of $L$. The conclusion: the set of points $s$ of $\operatorname{Spec} S$ such that for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$ with kernel the prime $s$, the map sending $c : \mathrm{Fin}(2g) \to \mathrm{Fin}\,n$ to the `finComb` product $\prod_i (P_i)^{c_i}$ of the base-changed sections along $\operatorname{Spec}(sk)$ is (i) injective and (ii) surjective onto the sections $Q$ over $\operatorname{Spec}(sk)$ with $n \cdot Q = 1$, is clopen in $\operatorname{Spec} S$.
--
--   This is the statement that the locus in the base where $2g$ given $n$-torsion sections form a full level-$n$ structure on the geometric fibres is open and closed, $n$ being invertible; the two clauses are exactly the independence and spanning conditions used in the definition of a framed polarised abelian scheme. It is used in the construction of the fine moduli space of framed polarised abelian schemes, in particular in the results producing a quasi-projective fine moduli space and a projective embedding over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_finComb_injective_and_forall_torsion_exists.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_finComb_injective_and_forall_torsion_exists
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      (∀ c c' : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
        c = c') ∧
      (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q)} := by sorry
