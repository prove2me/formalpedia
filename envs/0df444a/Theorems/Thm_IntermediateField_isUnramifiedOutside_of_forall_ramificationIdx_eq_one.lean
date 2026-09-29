-- Prove2me | Theorems.Thm_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one
-- name    : IntermediateField.isUnramifiedOutside_of_forall_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/be39d7cf-1dc2-5cbb-8ea1-8847f7214e34
-- title:
--   Ramification index one over an unramified base gives unramified outside S
-- statement:
--   Let $S$ be a finite set of rational primes, and let $L \subseteq F$ be intermediate fields of $\overline{\mathbb Q}/\mathbb Q$ (as $\mathbb Q$-subfields of `AlgebraicClosure ℚ`), each finite over $\mathbb Q$, with $F/L$ Galois, $F$ being regarded as an intermediate field of $\overline{\mathbb Q}/L$ via `IntermediateField.extendScalars`. Assume $L$ is unramified outside $S$ in the inertia reading: $L$ is finite over $\mathbb Q$ and, for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ (transported along the inclusion of the decomposition subgroup) is contained in the fixing subgroup of $L$. Assume further that for every height-one prime $w$ of $\mathcal O_F$ which lies over no prime of $S$, i.e. such that there is no $p \in S$ with $p \in w$, the ramification index $e$ of $w$ over its contraction $w \cap \mathcal O_L$, computed for the algebra structure induced by the inclusion $L \hookrightarrow F$, equals $1$. Then $F$ is unramified outside $S$ in the same inertia sense: $F$ is finite over $\mathbb Q$ and, for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a nonunit, the image of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup of $F$.
--
--   This is the passage from the arithmetic statement of unramifiedness (ramification indices equal to one at the finite places away from $S$) to the Galois-theoretic statement (inertia subgroups of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ above primes outside $S$ act trivially), carried out relative to a base field $L$ already known to be unramified outside $S$ and Galois below $F$. It is used in the construction of towers of fields unramified outside $S$, namely by [`IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one`](thm.html#IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

theorem IntermediateField.isUnramifiedOutside_of_forall_ramificationIdx_eq_one
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] (hL : L.IsUnramifiedOutside S)
    [IsGalois ↥L ↥(IntermediateField.extendScalars hLF)]
    (h : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes) →
      letI := (IntermediateField.inclusion hLF).toRingHom.toAlgebra
      Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ↥L)) w.asIdeal = 1) :
    F.IsUnramifiedOutside S := by sorry
