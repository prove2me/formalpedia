-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_theorem_5_1
-- name    : LowRankMisspec.RankOne.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:48.215221+00:00
-- url     : https://prove2.me/theorems/78835c84-086a-4b9d-94c1-87dba272e204
-- title:
--   Theorem 5.1 — proper rank-one agnostic learner: product law $H$ with $\|P-H\|_1\le 97\,d_1(P)+\eta$ w.p. $\ge1-\delta$, polynomial bit cost, exact sampling and evaluation
-- statement:
--   There are one program of the fair-coin log-cost RAM and one exponent $c$ such that for every $T\ge1$, every alphabet size $\sigma\ge1$, every rational $\eta\in(0,1]$, every rational $\delta\in(0,1/2)$ and **every** law $P$ on $[\sigma]^T$, the program run with $\mathrm{CondSamp}(P;\cdot)$ (Definition 2.2) on $[T,\sigma,\eta,\delta]$:
--   - halts on every run within log-cost $(T+\sigma+\lceil1/\eta\rceil+\lceil\log(1/\delta)\rceil+\text{input length}+2)^c$; this also bounds the number of oracle calls and the output length;
--   - always outputs a valid dyadic product code, so the returned law $H$ is a product law (hence in $\mathcal R_1$);
--   - returns, with probability at least $1-\delta$, an $H$ with
--   $$\|P-H\|_1\le 97\,d_1(P)+\eta,$$
--   where $d_1(P)=\min\{\|P-Q\|_1:Q\in\Delta([\sigma]^T),\ \mathrm{drank}(Q)\le1\}$.
--
--   Moreover there are an evaluation program, a sampling program and an exponent $c'$, using no oracle, such that for every valid code of a law $H$: the evaluator on (code, $x$) outputs $[\text{num},\text{den}]$ with $\text{num}/\text{den}=H[x]$, the sampler on the code outputs $x$ with probability exactly $H[x]$, and each halts on every run within $(\text{input length}+2)^{c'}$.
--
--   This is the paper's efficient positive result: proper agnostic learning of product laws with a constant-factor guarantee in time polynomial in $T,\sigma,1/\eta,\log(1/\delta)$, for an arbitrary target.
--
--   Differences from the source:
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: a distribution P ∈ Δ([σ]^T) → a real function P on Fin T → Fin σ with IsLaw P (nonnegative, summing to 1); reason: the simplex written out; same instances
--   - encoding: CondSamp access as in Definition 2.2; an algorithm → one Program of the published fair-coin log-cost RAM, run with the oracle condSamp P (⊥ = [0], continuation f = 1 :: f); reason: the paper's cost model: worst-case bit cost including reading oracle responses, fair random bits, exact rational arithmetic
--   - encoding: η ∈ (0, 1], δ ∈ (0, 1/2) → rational η, δ given as numerator/denominator cells in the input [T, σ, η, δ]; reason: an algorithm receives its parameters encoded
--   - reading: polynomially many oracle calls and worst-case bit cost polynomial in T, σ, 1/η, log(1/δ) → one universal c with HaltsWithin (T + σ + ⌈1/η⌉ + ⌈log(1/δ)⌉ + encLen input + 2)^c on every run; reason: the machine must read the rationals η, δ, whose encoding length is not bounded by 1/η, log(1/δ) (e.g. η = (2^1000 − 1)/2^1000); the log-cost bounds the oracle calls, the bit cost and the output length
--   - encoding: returns a product law H; the output is a proper distribution with a polynomial-size description → every output is encCode of a ValidCode (rows of numerators summing to 2^b), decoded by the fixed lawOfCode; reason: the paper's own output representation (p. 39); a valid code always decodes to a product law
--   - reading: from which we can sample and evaluate the probability of any string exactly in polynomial time, without further oracle calls → oracle-free evalProg and sampProg and one exponent c' with HaltsWithin (encLen input + 2)^{c'} on every run, exact output value and exact output law; reason: polynomial in the size of the description, which is the input of these programs
--   - encoding: d₁(P) = min_{Q ∈ R₁} ‖P − Q‖₁ → dR 1 P, the infimum over laws Q with drank Q ≤ 1 (drank via the ranks of J_t, Definition 2.1); reason: the minimum is attained (Proposition A.10); d₁ is not replaced by the distance to product laws
--   - generalization: exact sampling and evaluation for the learner's output → for every valid code (any T, σ, b and numerators with rows summing to 2^b), whether or not the learner produced it; reason: every output of the learner is a valid code, so the Lean clause specializes to the printed one
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 8 (PDF 9), Theorem 5.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Rank
import Definitions.Def_LowRankMisspec_RankOne_Machine

open PrefixMixLearn.Proper (Program HaltsWithin OutputsSatisfy outProb encLen)

namespace LowRankMisspec.RankOne

/-- Theorem 5.1 (proper rank-one agnostic learner). There are one fair-coin program and one
exponent `c` such that for every `T ≥ 1`, `σ ≥ 1`, rational `η ∈ (0, 1]`, rational `δ ∈ (0, 1/2)`
and every law `P` on `[σ]^T`, run with `CondSamp(P; ·)` on `[T, σ, η, δ]`: every run halts within
log-cost `(T + σ + ⌈1/η⌉ + ⌈log(1/δ)⌉ + encLen input + 2)^c`; every output is a valid dyadic
product code (so its law `H` is a product law); and with probability at least `1 − δ` the decoded
`H` satisfies `‖P − H‖₁ ≤ 97·d₁(P) + η`. Moreover there are oracle-free programs and an exponent
`c'` such that, for every valid code, the evaluator on `code ++ x` outputs `[num, den]` with
`num/den = H[x]`, and the sampler on `code` outputs `x` with probability exactly `H[x]`, each
halting on every run within `(encLen input + 2)^{c'}`. -/
theorem theorem_5_1 :
    (∃ (prog : Program) (c : ℕ),
      ∀ (T σ : ℕ) (η δ : ℚ), 1 ≤ T → 1 ≤ σ → 0 < η → η ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∀ (P : Str σ T → ℝ), IsLaw P →
        HaltsWithin prog (condSamp P) (learnerInput T σ η δ)
          (((T + σ + ⌈1 / (η : ℝ)⌉₊ + ⌈Real.log (1 / (δ : ℝ))⌉₊ +
            encLen (learnerInput T σ η δ) + 2 : ℕ) : ℝ) ^ c) ∧
        OutputsSatisfy prog (condSamp P) (learnerInput T σ η δ)
          (fun o => ∃ code : ProdCode σ T, o = encCode code ∧ ValidCode code) ∧
        1 - (δ : ℝ) ≤ outProb prog (condSamp P) (learnerInput T σ η δ)
          (fun o => ∃ code : ProdCode σ T, o = encCode code ∧ ValidCode code ∧
            l1 P (lawOfCode code) ≤ 97 * dR 1 P + η)) ∧
    (∃ (evalProg sampProg : Program) (c' : ℕ),
      ∀ (T σ : ℕ) (code : ProdCode σ T), ValidCode code →
        (∀ x : Str σ T,
          HaltsWithin evalProg nullOracle (encCode code ++ strCells x)
            (((encLen (encCode code ++ strCells x) + 2 : ℕ) : ℝ) ^ c') ∧
          OutputsSatisfy evalProg nullOracle (encCode code ++ strCells x)
            (fun o => ∃ num den : ℕ, o = [num, den] ∧ 0 < den ∧
              (num : ℝ) / den = lawOfCode code x)) ∧
        HaltsWithin sampProg nullOracle (encCode code)
          (((encLen (encCode code) + 2 : ℕ) : ℝ) ^ c') ∧
        ∀ x : Str σ T,
          outProb sampProg nullOracle (encCode code) (fun o => o = strCells x) =
            lawOfCode code x) := by sorry

end LowRankMisspec.RankOne
