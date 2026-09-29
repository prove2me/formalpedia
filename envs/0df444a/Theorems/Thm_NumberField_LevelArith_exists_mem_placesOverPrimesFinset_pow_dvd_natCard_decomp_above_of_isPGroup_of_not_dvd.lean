-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd
-- name    : NumberField.LevelArith.exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d133c878-191c-5359-96d8-998df17f0393
-- title:
--   Sylow placement of a large decomposition group
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes with $p \in S$, and let $L \le L_1 \le F$ be intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$ (the inclusions $L \le L_1$, $L_1 \le F$ and $L \le F$ being given separately), each finite over $\mathbb{Q}$, with $F/\mathbb{Q}$ normal. Assume that the quotient of the fixing subgroup of $L_1$ by the preimage in it of the fixing subgroup of $F$ — that is, $\mathrm{Gal}(F/L_1)$ — is a $p$-group, and that $p$ does not divide the $L$-dimension of $L_1$ regarded as an extension field of $L$ (the intermediate field `levelField L L₁ hLL₁` of $\overline{\mathbb{Q}}/L$ obtained from $L_1$ by extension of scalars). Let $k$ be a natural number and suppose that for every height-one prime $w$ of the ring of integers of $F$, viewed as an extension of $L$, whose ideal contains some rational prime of $S$, the integer $p^k$ divides the order of the decomposition subgroup $\mathrm{decomp}$ of $\mathrm{Gal}(F/L)$ at $w$, i.e. the subgroup stabilising the valuation subring attached to $w$. Then there is a height-one prime $v_0$ of the ring of integers of $L_1$ belonging to the finite set of primes whose ideal contains some rational prime of $S$, such that $p^k$ divides the order of the decomposition subgroup of $\mathrm{Gal}(F/L_1)$ at the place [`NumberField.PlaceAbove.above`](def/NumberField_PlaceAbove.html#L27) of $F$ (as an extension of $L_1$) chosen over $v_0$.
--
--   The statement is a Sylow placement argument for decomposition groups: since $\mathrm{Gal}(F/L_1)$ is a $p$-group of index prime to $p$ in $\mathrm{Gal}(F/L)$, it is a Sylow $p$-subgroup, and conjugating a Sylow subgroup of a decomposition group into it produces a place of $L_1$ over $S$ whose decomposition group in $F/L_1$ is still of order divisible by $p^k$, using transitivity of the Galois action on the primes above a given prime and the conjugacy of decomposition groups. It is used in the construction of a level at which a prescribed $S$-idele class coboundary condition holds, via [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L L₁ F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F : L₁ ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (hP : IsPGroup p (↥L₁.fixingSubgroup ⧸ F.fixingSubgroup.comap L₁.fixingSubgroup.subtype))
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L₁ hLL₁))
    (k : ℕ)
    (hk : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F hLF)),
      w ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F hLF) (S : Set Nat.Primes) →
      p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) :
    ∃ v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₁),
      v₀ ∈ placesOverPrimesFinset ↥L₁ S ∧
      p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L₁ ↥(levelField L₁ F hL₁F) (NumberField.PlaceAbove.above ↥L₁ ↥(levelField L₁ F hL₁F) v₀)) := by sorry
