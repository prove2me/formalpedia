-- Prove2me | Theorems.Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
-- name    : NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/f0577e4e-70ef-57a6-8356-02673602fb64
-- title:
--   S-units are units at valuation rings over primes outside S
-- statement:
--   Let $S$ be a finite set of rational primes and $S_{\mathbb Q}$ a finite set of height-one primes of $\mathcal O_{\mathbb Q}$ such that, as a set, $S_{\mathbb Q}$ equals [`NumberField.placesOverPrimes`](def/M4aHerbrand_SIdeleClassGroup.html#L313) of $S$, i.e. the set of height-one primes $w$ of $\mathcal O_{\mathbb Q}$ for which $(p : \mathcal O_{\mathbb Q}) \in w$ for some $p \in S$. Let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is a number field, and let $u \in F^{\times}$ lie in the subgroup [`NumberField.SUnits.sUnits`](def/NumberField_SUnitsModule.html#L25) attached to $S_{\mathbb Q}$, that is, the intersection over all $\mathbb Q$-algebra automorphisms $\sigma$ of $F$ of the preimages under $\sigma$ of the group `Set.unit` of the set of height-one primes $w$ of $\mathcal O_F$ whose restriction $w \cap \mathcal O_{\mathbb Q}$ lies in $S_{\mathbb Q}$; so each conjugate of $u$ is a unit away from the primes above $S_{\mathbb Q}$. Let $q$ be a prime not in $S$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `LiesOverPrime` $q$, meaning that the image of $q$ in $\overline{\mathbb Q}$ is a nonunit of $A$. Then the image of $u$ under $F \to \overline{\mathbb Q}$ lies in $A$, and so does its inverse.
--
--   This is the standard statement that an $S$-unit of a number field is a unit in every valuation ring of $\overline{\mathbb Q}$ whose centre lies over a rational prime outside $S$. It serves as the bridge between the $S$-units of a finite level $F$ and $S$-unit conditions formulated over $\overline{\mathbb Q}$, and is used in the construction of $S$-level extensions and of $p$-th root / Herbrand-quotient arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
    (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (u : (↥F)ˣ) (hu : u ∈ NumberField.SUnits.sUnits ℚ ↥F Sℚ)
    (q : Nat.Primes) (hq : q ∉ S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime (q : ℕ)) :
    algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F) ∈ A ∧ (algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F))⁻¹ ∈ A := by sorry
