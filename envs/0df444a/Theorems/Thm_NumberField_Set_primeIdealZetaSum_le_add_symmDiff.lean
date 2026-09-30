-- Prove2me | Theorems.Thm_NumberField_Set_primeIdealZetaSum_le_add_symmDiff
-- name    : NumberField.Set.primeIdealZetaSum_le_add_symmDiff
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:39:18.300684+00:00
-- url     : https://prove2.me/theorems/99a06c56-7a33-48ea-a192-685027c62a3b
-- title:
--   Changing a set by a small symmetric difference changes the sum by little
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $S,T$ be sets of nonzero prime ideals and let $s\in\mathbb R$. Put $P_U(s)=\sum_{P\in U}N(P)^{-s}$. If the sums over $T$ and $S\mathbin\triangle T$ converge, then
--
--   $$
--   P_S(s)\le P_T(s)+P_{S\mathbin\triangle T}(s).
--   $$
--
--   This quantifies the effect of changing a prime set on its prime zeta sum.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/ZetaSumPartition.lean#L111-L130), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/ZetaSumPartition.lean#L111-L130

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.NumberTheory.NumberField.DirichletDensity

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Partitioning the partial Dirichlet series over a set of primes

Let `K` be a number field. Mathlib's partial Dirichlet series `NumberField.Set.primeIdealZetaSum`
sums `𝔑𝔭 ^ (-s)` over a set of nonzero prime ideals of `𝓞 K`, and this file cuts that sum along a
partition of the primes. The sum is additive along a finite pairwise disjoint union, given
summability on each piece, and subadditive along an arbitrary union of two sets. For a finite
set `S` of primes it also compares the sum over the complement `Sᶜ` with the sum over all primes:
deleting `S` never increases the sum, and for `s ≥ 0` it lowers it by at most the number of
primes deleted.

## Main results

* `NumberField.Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint`: given summability on each
  piece, the sum over a finite pairwise disjoint union is the sum of the sums over the pieces.
* `NumberField.Set.primeIdealZetaSum_union_le`: given summability on both sets, the sum over a
  union is at most the sum of the two sums.
* `NumberField.Set.primeIdealZetaSum_le_add_symmDiff`: given summability over `T` and over
  `S ∆ T`, the sum over `S` exceeds the sum over `T` by at most the sum over `S ∆ T`.
* `NumberField.Set.primeIdealZetaSum_compl_le_univ_of_finite`: deleting a finite set of primes
  does not increase the sum.
* `NumberField.Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite`: for `s ≥ 0`, deleting a
  finite set of primes lowers the sum by at most `S.ncard`.

## Implementation notes

`primeIdealZetaSum S s` is a `tsum`, so it takes the value `0` on a family that is not summable.
That junk value is not additive along a partition, which is why the disjoint-union identity
carries a summability hypothesis.

The same junk value, together with `Set.ncard` being `0` on an infinite set, makes finiteness of
`S` essential to the two complement statements rather than a convenience, and both fail without
it. Take `S = {𝔭₀}ᶜ`, which is itself infinite and whose complement `{𝔭₀}` is a single prime. At
`s = 0` every term is `1`, so the sum over all primes diverges and is read as `0` while the sum
over `{𝔭₀}` is `1`: the first bound reads `1 ≤ 0`. At `s = 2` both sums converge while `S.ncard`
is read as `0`, so the second bound reads `(∑' 𝔭, 𝔑𝔭 ^ (-2)) - 𝔑𝔭₀ ^ (-2) ≤ 0`, whose left-hand
side is the positive sum over the primes other than `𝔭₀`.

## References

The corresponding statements for a source-local `primeIdealZetaSum` over `Set (Ideal (𝓞 K))` are
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_union_of_disjoint` and
`primeIdealZetaSum_le_of_subset` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. Those are gated on `1 < s`;
the statements here take the weaker hypotheses that each proof actually uses — summability on the
participating pieces for the disjoint-union identity, finiteness for the two complement bounds.
-/

 section

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

open IsDedekindDomain (HeightOneSpectrum)
open scoped symmDiff

-- `primeIdealZetaSum` lives in `NumberField.Set`, so dot notation on a set of primes finds it
-- only while `NumberField` is open.
open NumberField

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

theorem NumberField.Set.primeIdealZetaSum_le_add_symmDiff {S T : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hT : _root_.Summable fun 𝔭 : T ↦ (_root_.Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    (hST : _root_.Summable fun 𝔭 : ↥(S ∆ T) ↦ (_root_.Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s + (S ∆ T).primeIdealZetaSum s := by sorry
