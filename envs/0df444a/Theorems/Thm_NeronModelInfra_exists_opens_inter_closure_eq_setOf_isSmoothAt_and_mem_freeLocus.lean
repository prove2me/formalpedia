-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
-- name    : NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/cf07daf9-4aa2-5be6-a9ca-52a134e7b7f0
-- title:
--   Openness of the smooth–free stratum on an affine chart
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), let $f : X \to \operatorname{Spec} R$ be a morphism of schemes that is locally of finite type, and let $S \subseteq X$ be a set of points subject to two hypotheses: (i) every $s \in S$ is of the form $x(\mathfrak{m}_{R'})$, where $R'$ is a discrete valuation ring equipped with a local $R$-algebra structure such that $\mathfrak{m}_R R' = \mathfrak{m}_{R'}$ and the residue field extension $k(R) \to k(R')$ is formally smooth (the predicate `IsIndexOneExtension`), and $x : \operatorname{Spec} R' \to X$ is a morphism with $x$ followed by $f$ equal to $\operatorname{Spec}$ of $R \to R'$; and (ii) every $s \in S$ satisfies $f(s) = \mathfrak{m}_R$, i.e. lies in the special fibre. Fix an affine open $U \subseteq X$, write $A = \Gamma(X, U)$ with the $R$-algebra structure induced by $f$, and let $J \subseteq A$ be the ideal of elements vanishing at all primes of $A$ corresponding to points of $U$ lying in $\overline{S}$. Then there is an open $W \subseteq X$ with $W \subseteq U$, such that $\overline{S} \cap U \ne \emptyset$ implies $\overline{S} \cap W \ne \emptyset$, and such that for $y \in U \cap \overline{S}$ one has $y \in W$ if and only if the prime $\mathfrak{q}$ of $A/J$ contracting to the prime of $y$ satisfies both: $A/J$ is smooth at $\mathfrak{q}$ over the residue field of $R$ (asserted for every $k(R)$-algebra structure on $A/J$ compatible with the $R$-structure), and $\mathfrak{q}$ lies in the free locus of the $A/J$-module $(A/J) \otimes_A \Omega_{A/R}$.
--
--   This is the chart-level openness statement underlying the construction of weak Néron models: on an affine chart, the locus of points of the closure of a set of index-one sections at which the reduced special-fibre closure is smooth over the residue field and the differentials become free is open and still meets that closure. It is used by [`NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd`](thm.html#NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd), and rests on the translation of index-one points into local $R$-algebra maps from $A$ together with the openness criterion [`Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset`](thm.html#Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (hSk : ∀ s ∈ S, f s = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S})
    ∃ W : X.Opens, (W : Set X) ⊆ U ∧
      ((closure S ∩ (U : Set X)).Nonempty → (closure S ∩ (W : Set X)).Nonempty) ∧
      ∀ (y : X) (hyU : y ∈ U), y ∈ closure S →
        (y ∈ W ↔
          ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
            𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
            (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
              [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
              Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
            (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
              Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) := by sorry
