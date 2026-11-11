-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_corollary_D_2
-- name    : LowRankMisspec.RankOne.corollary_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:36.289316+00:00
-- url     : https://prove2.me/theorems/e2c97a23-e67f-46d7-821b-37178e3f5bad
-- title:
--   Corollary D.2 — finite-family TV validation: all $M$ distances to accuracy $a$ w.p. $\ge1-\delta$ with $O(T^2\sigma a^{-4}\log(2M)\log(2/\delta))$ CondSamp calls
-- statement:
--   There are one program of the fair-coin log-cost RAM, one constant $C$ and one exponent $c$ such that for all $T,\sigma,M$, all rationals $a,\delta\in(0,1)$, every list of laws $H_1,\dots,H_M$ on $[\sigma]^T$ with rational values, specified only through exact evaluation of $H_j[x]$, and every law $P$, reached only through CondSamp, the program run on $[T,\sigma,M,a,\delta]$:
--   - outputs estimates $\hat D_1,\dots,\hat D_M$ with
--   $$\Pr\Big[\max_{j\le M}\big|\hat D_j-\|P-H_j\|_1\big|\le a\Big]\ge1-\delta;$$
--   - makes on every run at most $C\,\dfrac{T^2\sigma}{a^4}\log(2M)\log\dfrac2\delta$ CondSamp calls;
--   - halts on every run within log-cost $(T+\sigma+M+\lceil1/a\rceil+\lceil\log(2/\delta)\rceil+\mathrm{valBits}(H)+\text{input length}+2)^c$, where $\mathrm{valBits}(H)$ is the largest bit length of a candidate value.
--
--   The algorithm never samples from the $H_j$. Theorem 5.1 uses it to choose among its candidate product laws.
--
--   Differences from the source:
--   - generalization: §2.1 fixes σ, T ≥ 2; candidates H_1, …, H_M (M ≥ 1) → every T, σ, M ≥ 0; reason: at T = 0 every law is the same point mass and at M = 0 there is nothing to estimate, both with zero calls; at σ, T ≥ 2, M ≥ 1 the Lean statement is the source's
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a, δ ∈ (0, 1) → rational a, δ given as numerator/denominator cells in the input [T, σ, M, a, δ]; reason: an algorithm receives its parameters encoded
--   - encoding: H_j specified so that H_j[x] can be computed; CondSamp access to P → one oracle valOracle P H: 0 :: h is CondSamp(P; h), 1 :: j :: x returns [num, den] of H_{j+1}[x]; H_j rational-valued laws; reason: the only access to P and to the candidates
--   - encoding: worst-case number of oracle calls O(T²σ/a⁴ · log(2M) log(2/δ)) → at most C·T²·σ/a⁴·log(2M)·log(2/δ) queries of the form 0 :: h on every run, C universal; reason: the O(·) as an explicit universal constant; candidate evaluations are computations, not CondSamp calls
--   - reading: if the probabilities can be computed exactly in polynomial time using rational arithmetic, the procedure has polynomial bit complexity → HaltsWithin (T + σ + M + ⌈1/a⌉ + ⌈log(2/δ)⌉ + valBits H + encLen input + 2)^c on every run; reason: exact evaluation is an oracle reply whose bit length valBits H is charged; the input length enters because rational a, δ are read
--   - reading: the guarantee also applies to randomly constructed candidates fixed before validation, with fresh samples and independent randomness → the guarantee for every fixed list H; reason: the random-candidate clause follows by conditioning on the candidates
--   - encoding: estimates D̂_j → rationals output as cells [sign, |num|, den]; reason: output encoding
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 32 (PDF 33), Corollary D.2

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Machine

open PrefixMixLearn.Proper (Program HaltsWithin outProb encLen)

namespace LowRankMisspec.RankOne

/-- Corollary D.2 (finite-family TV validation with CondSamp). There are one fair-coin program, one
constant `C` and one exponent `c` such that for all `T`, `σ`, `M`, `a, δ ∈ (0, 1)` (rational), every
list of rational laws `H_1, …, H_M` on `[σ]^T` (reached only through exact evaluations
`1 :: j :: x ↦ H_{j+1}[x]`) and every law `P` (reached only through `CondSamp`, queries `0 :: h`),
run on `[T, σ, M, a, δ]`: with probability at least `1 − δ` it outputs estimates `D̂_1, …, D̂_M`
with `max_j |D̂_j − ‖P − H_j‖₁| ≤ a`; on every run it makes at most
`C·T²σ/a⁴·log(2M)·log(2/δ)` CondSamp calls; and every run halts within log-cost
`(T + σ + M + ⌈1/a⌉ + ⌈log(2/δ)⌉ + valBits H + encLen input + 2)^c`. -/
theorem corollary_D_2 :
    ∃ (prog : Program) (C : ℝ) (c : ℕ),
      ∀ (T σ M : ℕ) (a δ : ℚ), 0 < a → a < 1 → 0 < δ → δ < 1 →
      ∀ (H : Fin M → Str σ T → ℚ), (∀ j, IsLaw fun x => (H j x : ℝ)) →
      ∀ (P : Str σ T → ℝ), IsLaw P →
        1 - (δ : ℝ) ≤ outProb prog (valOracle P H) (valInput T σ M a δ)
          (fun o => ∃ D : Fin M → ℚ, o = estCells D ∧
            ∀ j, |(D j : ℝ) - l1 P (fun x => (H j x : ℝ))| ≤ a) ∧
        QueriesWhereWithin prog (valOracle P H) (valInput T σ M a δ) (fun q => q.head? = some 0)
          (C * (T : ℝ) ^ 2 * σ / (a : ℝ) ^ 4 * Real.log (2 * M) * Real.log (2 / (δ : ℝ))) ∧
        HaltsWithin prog (valOracle P H) (valInput T σ M a δ)
          (((T + σ + M + ⌈1 / (a : ℝ)⌉₊ + ⌈Real.log (2 / (δ : ℝ))⌉₊ + valBits H +
            encLen (valInput T σ M a δ) + 2 : ℕ) : ℝ) ^ c) := by sorry

end LowRankMisspec.RankOne
