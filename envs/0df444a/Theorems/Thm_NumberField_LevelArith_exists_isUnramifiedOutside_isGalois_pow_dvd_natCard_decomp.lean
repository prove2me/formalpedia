-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- name    : NumberField.LevelArith.exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/33192690-a041-57e6-a7af-f29f1419ad58
-- title:
--   Galois S-levels with p^k-divisible local degrees above S
-- statement:
--   Let $p$ be a prime and let $S$ be a finite set of primes containing $p$. Let $L$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is unramified outside $S$ in the sense of `IsUnramifiedOutside`: $L$ is finite over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$, transported into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ along the inclusion of the decomposition subgroup of $A$, lies in the fixing subgroup of $L$. Let $k$ be a natural number. The assertion is that there is an intermediate field $F$ with $L \le F$, again unramified outside $S$ in the above sense (so in particular finite over $\mathbb{Q}$), and Galois over $\mathbb{Q}$, with the following property. Write $F$ as an extension of $L$ via `levelField L F hLF` ($F$ with scalars extended to $L$), and let $w$ be a height-one prime of the ring of integers of this field lying over $S$, i.e. such that some $q \in S$ satisfies $q \in w$. Then $p^k$ divides the order of [`NumberField.PlaceDecomp.decomp`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup at $w$ inside $\mathrm{Gal}(F/L)$, namely the stabiliser in $\mathrm{Gal}(F/L)$ of the valuation subring attached to the $w$-adic valuation.
--
--   This is the statement that over a given $S$-level $L$ there exist arbitrarily deep Galois $S$-levels, all of whose local degrees at the places above $S$ are divisible by a prescribed power of $p$; the classical source of such fields is the tower of $p$-power cyclotomic extensions, admissible because $p \in S$. It supplies the "enough depth" input for the passage to the limit in the local-invariant description of the $p$-part of $H^2$ of the $S$-ramified Galois group, and is used by [`NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp) and by the construction of idele classes with prescribed local invariants from a sum-zero family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] (k : ℕ) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : F.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F),
      ∀ [FiniteDimensional ℚ ↥F] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F hLF))),
        w ∈ placesOverPrimes ↥(levelField L F hLF) (S : Set Nat.Primes) →
        p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w) := by sorry
