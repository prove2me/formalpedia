-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_rounding_claim
-- name    : LowRankMisspec.RankOne.rounding_claim
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:01.107059+00:00
-- url     : https://prove2.me/theorems/518d3ee3-faa0-48ea-8cd5-c13398a0e310
-- title:
--   §E.2 rounding claim — largest-remainder rounding to $2^{-b}$: sum kept, coordinates within $2^{-b}$, zeros kept, product moves $\le T\sigma2^{-b}\le\eta/2$
-- statement:
--   Let $b\ge0$. To round a row $p\in\Delta([\sigma])$, floor each $2^bp[a]$ and allocate the remaining $R=2^b-\sum_a\lfloor2^bp[a]\rfloor$ units to the largest fractional remainders (ties broken in any way). Then the numerators sum to $2^b$, every coordinate changes by at most $2^{-b}$, zeros are preserved, and if units remain ($R>0$), $R$ is strictly less than the number of positive fractional remainders. Rounding each of $T$ rows changes the product law by at most
--   $$\Big\|\bigotimes_t p_t-\bigotimes_t\tfrac{n_t}{2^b}\Big\|_1\le T\sigma2^{-b},$$
--   and for $\eta\in(0,1]$ and $b=\lceil\log_2(2T\sigma/\eta)\rceil$ (the choice of Theorem 5.1's step 4), $T\sigma2^{-b}\le\eta/2$. This is what makes the learner's output an exactly representable product law.
--
--   Differences from the source:
--   - generalization: §2.1 fixes an alphabet and length with σ, T ≥ 2 → every T ≥ 0 and σ ≥ 0 (an empty alphabet with T ≥ 1 admits no law, so the statement is then vacuous); reason: the result's own statement carries no size condition and its proof uses none; at σ, T ≥ 2 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - reading: allocate the remaining units to the largest fractional remainders → every n with IsLRRounding b p n, i.e. for every tie-break among equal remainders; reason: the paper fixes no tie-break, so the claim is read for all of them
--   - reading: Tσ2^{−b} ≤ η/2, with b defined in step 4 of the proof (p. 38) → a separate conjunct for η ∈ (0, 1] and b = ⌈log₂(2Tσ/η)⌉₊; reason: the inequality holds for that b, which is the b of the claim
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 39 (PDF 40), §E.2, rounding claim

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rounding

namespace LowRankMisspec.RankOne

/-- §E.2, rounding claim: a largest-remainder rounding `n` of a row `p ∈ Δ([σ])` to denominator
`2^b` has numerators summing to `2^b`, moves each coordinate by at most `2^{−b}`, keeps zeros, and,
if `R = 2^b − Σ_a ⌊2^b p[a]⌋` units remain, `R` is less than the number of positive fractional
remainders; rounding each of `T` rows moves the product law by at most `Tσ2^{−b}` in ℓ1; and for
`η ∈ (0, 1]` and `b = ⌈log₂(2Tσ/η)⌉`, `Tσ2^{−b} ≤ η/2`. -/
theorem rounding_claim {σ T : ℕ} (b : ℕ) :
    (∀ (p : Fin σ → ℝ) (n : Fin σ → ℕ), IsLaw p → IsLRRounding b p n →
      ∑ a, n a = 2 ^ b ∧
      (∀ a, |dyadicRow b n a - p a| ≤ 1 / 2 ^ b) ∧
      (∀ a, p a = 0 → n a = 0) ∧
      (0 < 2 ^ b - ∑ a, ⌊(2 : ℝ) ^ b * p a⌋₊ →
        2 ^ b - ∑ a, ⌊(2 : ℝ) ^ b * p a⌋₊ <
          (Finset.univ.filter fun a => 0 < Int.fract ((2 : ℝ) ^ b * p a)).card)) ∧
    (∀ (p : Fin T → Fin σ → ℝ) (n : Fin T → Fin σ → ℕ), (∀ t, IsLaw (p t)) →
      (∀ t, IsLRRounding b (p t) (n t)) →
      l1 (prodLaw p) (prodLaw fun t => dyadicRow b (n t)) ≤ (T : ℝ) * σ / 2 ^ b) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 → b = ⌈Real.logb 2 (2 * T * σ / η)⌉₊ →
      (T : ℝ) * σ / 2 ^ b ≤ η / 2) := by sorry

end LowRankMisspec.RankOne
