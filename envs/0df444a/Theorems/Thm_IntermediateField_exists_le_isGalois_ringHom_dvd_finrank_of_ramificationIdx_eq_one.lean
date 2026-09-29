-- Prove2me | Theorems.Thm_IntermediateField_exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one
-- name    : IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/3d67937e-d45d-5be3-8aed-b743cb407439
-- title:
--   Embedding an abstract S-unramified Galois extension into a Galois S-level
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes with $p \in S$ (as the element `pPrime p` of `Nat.Primes`). Let $L'$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is a number field and satisfies `IsUnramifiedOutside S`, i.e. $L'$ is finite-dimensional over $\mathbb Q$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ in the nonunits of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ is contained in the fixing subgroup of $L'$. Let $F_0$ be a number field which is an $L'$-algebra, Galois over $L'$, and assume that every height-one prime $w$ of $\mathcal O_{F_0}$ outside `placesOverPrimes F₀ S` — that is, with $q \notin w$ for all $q \in S$ viewed in $\mathcal O_{F_0}$ — has ramification index $1$ over the prime $w \cap \mathcal O_{L'}$ of $\mathcal O_{L'}$. Then there exist an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ with $L' \le F$, which is a number field and Galois over $\mathbb Q$, and a ring homomorphism $e : F_0 \to F$ restricting on $L'$ to the inclusion $L' \hookrightarrow F$, such that $F$ satisfies `IsUnramifiedOutside S` and $p$ divides $[F : L']$, the $L'$-rank of $F$ regarded as an extension of $L'$ via `extendScalars`.
--
--   This is the step which realises an abstractly given finite Galois extension $F_0/L'$, unramified outside $S$ in the sense of ramification indices, as a subfield of $\overline{\mathbb Q}$ contained in a finite Galois $S$-level $F/\mathbb Q$ whose degree over $L'$ is divisible by $p$. It feeds the construction of Galois levels with prescribed behaviour of $S$-class actions, being cited by [`IntermediateField.exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow`](thm.html#IntermediateField.exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one.lean

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

theorem IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L'] (hL' : L'.IsUnramifiedOutside S)
    (F₀ : Type) [Field F₀] [NumberField F₀] [Algebra ↥L' F₀] [IsGalois ↥L' F₀]
    (hunr : ∀ w : HeightOneSpectrum (𝓞 F₀), w ∉ NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes) →
      Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ↥L')) w.asIdeal = 1) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L' ≤ F) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F) (e : F₀ →+* ↥F),
      (∀ x : ↥L', e (algebraMap ↥L' F₀ x) = IntermediateField.inclusion hLF x) ∧
      F.IsUnramifiedOutside S ∧ p ∣ Module.finrank ↥L' ↥(IntermediateField.extendScalars hLF) := by sorry
