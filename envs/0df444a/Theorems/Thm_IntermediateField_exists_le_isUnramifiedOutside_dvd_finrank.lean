-- Prove2me | Theorems.Thm_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank
-- name    : IntermediateField.exists_le_isUnramifiedOutside_dvd_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/612ac450-c863-56e7-adc7-a57c7a00a782
-- title:
--   Above any S-level lies an S-level of relative degree divisible by p
-- statement:
--   Fix a natural number $p$ that is prime, and a finite set $S$ of rational primes containing $p$ (the hypothesis is that the prime `pPrime p`, namely $p$ together with its primality, belongs to $S$). Let $L'$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, and assume $L'$ is unramified outside $S$ in the following sense: $L'$ is finite over $\mathbb{Q}$, and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$, under the inclusion of the decomposition subgroup, is contained in the subgroup fixing $L'$ pointwise. The conclusion asserts the existence of an intermediate field $M$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ together with an inclusion $h : L' \le M$ such that $M$ again satisfies this unramified-outside-$S$ condition (so in particular $M/\mathbb{Q}$ is finite) and such that $p$ divides the dimension of $M$, viewed via `extendScalars h` as an extension of $L'$, as an $L'$-module, i.e. $p \mid [M : L']$.
--
--   This is the step which guarantees that the tower of fields unramified outside $S$ can always be enlarged with relative degree divisible by $p$, using only the cyclotomic fields $\mathbb{Q}(\zeta_{p^{k}})$ and the hypothesis $p \in S$, rather than any class-field-theoretic non-divisibility input. It feeds the construction of a Galois $S$-level extension with prescribed relative degree, [`IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one`](thm.html#IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank.lean

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

theorem IntermediateField.exists_le_isUnramifiedOutside_dvd_finrank
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L'] (hL' : L'.IsUnramifiedOutside S) :
    ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : L' ≤ M),
      M.IsUnramifiedOutside S ∧ p ∣ Module.finrank ↥L' ↥(IntermediateField.extendScalars h) := by sorry
