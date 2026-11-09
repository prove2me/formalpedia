-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_4_1
-- name    : KnapsackFPRAS.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:33.169965+00:00
-- url     : https://prove2.me/theorems/553b521c-1077-44fb-9435-a432b929b707
-- title:
--   Lemma 4.1 — properties of the random rounding: error $\le s_m\le S$, multiples of $\tau$, independent centered errors with $\mathrm{Var}\le S^2w(X)/T$
-- statement:
--   Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)), and let $B=2^b$ with $b\ge1$. Let $a$ be the randomly rounded weight vector (each $a_i$ rounded independently as in §4.2), $S=T/B$, $\tau=T/B^2$. Then:
--
--   1. for every ordinary class $I_m$, $m\in\{2,4,\dots,B^2\}$, and every $i\in I_m$, almost surely $|a_i-w_i|\le s_m\le S$ and $a_i\le2w_i$;
--   2. almost surely every $a_i$ is a nonnegative integer multiple of $\tau$;
--   3. for every fixed $X\subseteq[n]$, the errors $a_i-w_i$, $i\in X$, are independent, integrable, of mean zero and almost surely of magnitude at most $S$, and
--   $$
--   \operatorname{Var}\bigl(a(X)-w(X)\bigr)\le\frac{S^2\,w(X)}{T}.
--   $$
--
--   These are the facts about the rounding that the rest of the analysis uses: the rounded weights live on a grid of spacing $\tau$, and the rounding error of any fixed subset is a sum of independent, bounded, centered terms with controlled variance.
--
--   Differences from the source:
--   - reading: the lemma as printed in §4 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9)
--   - generalization: B the smallest power of two with B ≥ ℓκC_B, (14) → any B = 2^b with b ≥ 1; reason: the lemma's proof uses only that B is a power of two; the paper's B is one
--   - encoding: statements about the rounded weights → statements almost surely under the product law Rounding.roundLaw B T w; reason: the law has finite support, so almost surely is every realization
--   - encoding: independent mean-zero random variables → iIndepFun of (aᵢ − wᵢ)_{i∈X}, Integrable and ∫ (aᵢ − wᵢ) = 0; reason: integrability follows from the magnitude bound and makes the mean a genuine expectation
--   - encoding: ordinary classes m ∈ {2, 4, …, B²} → m = 2^j with 1 ≤ j ≤ 2b, s_m = Rounding.spacing B T j; reason: same classes
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 4.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_KnapsackFPRAS_Rounding

set_option autoImplicit false

namespace KnapsackFPRAS

open MeasureTheory ProbabilityTheory

/-- **Lemma 4.1**, p.15. "The rounded weights satisfy the following. 1. Every ordinary item
𝑖 ∈ 𝐼_𝑚 satisfies |𝑎𝑖 − 𝑤𝑖| ≤ 𝑠_𝑚 ≤ 𝑆 and 𝑎𝑖 ≤ 2𝑤𝑖. 2. Every 𝑎𝑖 is a nonnegative integer
multiple of 𝜏. 3. For every fixed 𝑋 ⊆ [𝑛], the rounding error 𝑎(𝑋) − 𝑤(𝑋) = ∑_{𝑖∈𝑋}(𝑎𝑖 − 𝑤𝑖)
is a sum of independent mean-zero random variables, each of magnitude at most 𝑆, and satisfies
Var(𝑎(𝑋) − 𝑤(𝑋)) ≤ 𝑆²𝑤(𝑋)/𝑇."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 4.1, p.15 (PDF p.16).

**Formalization Note.** Under the standing assumption (7), for every power of two `B = 2^b`,
`b ≥ 1` (the paper's `B` of (14) is one). The rounded vector `a` has the product law
`Rounding.roundLaw B T w`; clauses 1 and 2 hold for almost every `a` (equivalently, for every
value in the finite support). The ordinary classes are `m = 2^j`, `1 ≤ j ≤ 2b`
(`m ∈ {2, 4, …, B²}`), with `s_m = Rounding.spacing B T j`. Clause 3: for each `X`, the
errors `aᵢ − wᵢ` (`i ∈ X`) are mutually independent, integrable, of mean `0`, of magnitude at
most `S` almost surely, and the variance of their sum is at most `S² w(X)/T`. -/
theorem lemma_4_1 {n : ℕ} (w : Fin n → ℕ) (T : ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ T) (hsum : T < ∑ i, w i)
    (b : ℕ) (hb : 1 ≤ b) (B : ℕ) (hB : B = 2 ^ b) :
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * b → ∀ i ∈ Rounding.classIdx T w ((2 : ℝ) ^ j),
      ∀ᵐ a ∂(Rounding.roundLaw B T w),
        |a i - (w i : ℝ)| ≤ Rounding.spacing B T j ∧ Rounding.spacing B T j ≤ Rounding.S B T ∧
        a i ≤ 2 * (w i : ℝ)) ∧
    (∀ᵐ a ∂(Rounding.roundLaw B T w), ∀ i, ∃ z : ℕ, a i = z * Rounding.τ B T) ∧
    (∀ X : Finset (Fin n),
      iIndepFun (fun (i : X) (a : Fin n → ℝ) => a i - (w i : ℝ)) (Rounding.roundLaw B T w) ∧
      (∀ i ∈ X, Integrable (fun a : Fin n → ℝ => a i - (w i : ℝ)) (Rounding.roundLaw B T w) ∧
        ∫ a, (a i - (w i : ℝ)) ∂(Rounding.roundLaw B T w) = 0 ∧
        ∀ᵐ a ∂(Rounding.roundLaw B T w), |a i - (w i : ℝ)| ≤ Rounding.S B T) ∧
      variance (fun a : Fin n → ℝ => ∑ i ∈ X, (a i - (w i : ℝ))) (Rounding.roundLaw B T w) ≤
        Rounding.S B T ^ 2 * (∑ i ∈ X, (w i : ℝ)) / T) := by sorry

end KnapsackFPRAS
