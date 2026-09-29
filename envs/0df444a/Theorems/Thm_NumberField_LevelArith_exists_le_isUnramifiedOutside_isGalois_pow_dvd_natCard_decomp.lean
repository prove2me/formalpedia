-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- name    : NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/a21db1c3-60f8-5010-9d75-b53846dec27b
-- title:
--   Galois S-levels above a given level with p^k dividing decomposition orders
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$. Let $L$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$) which is finite over $\mathbb{Q}$ and unramified outside $S$, in the sense that $L$ is finite over $\mathbb{Q}$ and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$. Let $F$ be a further intermediate field, finite over $\mathbb{Q}$, unramified outside $S$ in the same sense, with $L \leq F$, and let $k$ be a natural number. The assertion is that there is an intermediate field $F_1$ with $L \leq F_1$ and $F \leq F_1$, finite over $\mathbb{Q}$, unramified outside $S$, and Galois over $\mathbb{Q}$, such that for every height-one prime $w$ of the ring of integers of $F_1$ regarded as an extension of $L$ (the scalar extension $\mathrm{levelField}\ L\ F_1$) with $p' \in w$ for some $p' \in S$, the power $p^k$ divides the cardinality of the decomposition subgroup of $w$ inside $\mathrm{Gal}(F_1/L)$, i.e. the stabiliser of the valuation subring attached to $w$.
--
--   This is the form, relative to a prescribed intermediate layer, of the statement that one may find $S$-levels over $L$ whose decomposition groups at the places above $S$ have order divisible by an arbitrarily high power of $p$; it supplies the deep Galois level used in the construction of $S$-idele classes with prescribed local behaviour. It is cited in the proof of [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp.lean

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
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand
open NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) (k : ℕ) :
    ∃ (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₁ : L ≤ F₁) (_ : F ≤ F₁) (hfd : FiniteDimensional ℚ ↥F₁)
      (_ : F₁.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₁),
      haveI := hfd
      ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F₁ hLF₁))),
        w ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F₁ hLF₁) (S : Set Nat.Primes) →
        p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F₁ hLF₁) w) := by sorry
