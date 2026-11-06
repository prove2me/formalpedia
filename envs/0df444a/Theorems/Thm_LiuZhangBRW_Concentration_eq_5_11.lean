-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_eq_5_11
-- name    : LiuZhangBRW.Concentration.eq_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:00.749009+00:00
-- url     : https://prove2.me/theorems/766a118f-cd33-409f-8053-b11561103d0e
-- title:
--   (5.11), proof of Lemma 5.3 — $\mathbb E_{i-1}[e^{\delta|\Delta_i|}]\le K^2$
-- statement:
--   Let $X_1,X_2,\dots$ be real random variables on a probability space, measurable for $1\le i\le n$, with $\mathbb E_i=\mathbb E(\cdot\mid X_1,\dots,X_i)$. Let $N\ge1$, $n\le M$, $\delta>0$, $L\ge0$, $K\in\mathbb R$ and
--   $$
--   A=1+L\,\frac MN .
--   $$
--   Assume
--
--   1. the Lipschitz condition (5.7): $\bigl|\mathbb E_{i-1}(X_\ell\mid X_i)-\mathbb E_{i-1}(X_\ell\mid X_i')\bigr|\le L|X_i-X_i'|/N$ for $1\le i<\ell\le n$, with $X_i'$ a conditionally independent copy of $X_i$ given $X_1,\dots,X_{i-1}$;
--   2. the finite MGF condition: $e^{\delta A|X_i|}$ is integrable and $\mathbb E_{i-1}\bigl[e^{\delta A|X_i|}\bigr]\le K$ almost surely, for $1\le i\le n$.
--
--   Then, for every $1\le i\le n$, Doob's increment $\Delta_i=\mathbb E_i(X_i+\dots+X_n)-\mathbb E_{i-1}(X_i+\dots+X_n)$ has $e^{\delta|\Delta_i|}$ integrable and, almost surely,
--   $$
--   \mathbb E_{i-1}\bigl[e^{\delta|\Delta_i|}\bigr]\le K^2.\tag{5.11}
--   $$
--
--   This is the conditional exponential-moment bound on the martingale increments that feeds the Chernoff argument of Lemma 5.3.
--
--   **Formalization Note** The Lipschitz condition is `IsLipschitzInIncrement μ X i ℓ (L / N)`; $\Delta_i$ is `doobIncrement μ X n i`.
--
--   Differences from the source:
--   - reading: (5.5)/(5.7)/(6.9) with X′_i a conditionally independent copy of X_i given X_1, ..., X_{i−1} → IsLipschitzInIncrement: a version g of E_i X_ℓ as a function of (past, X_i) satisfies |g(p,x) − g(p,x′)| ≤ (L/N)|x − x′| for almost every past p and almost every pair (x, x′) drawn from the product of the conditional law of X_i given p with itself; reason: this is how the proof of Lemma 5.2 (pp. 9–10) uses the condition; demanding the bound for every x, x′ of one version would be a stronger hypothesis
--   - encoding: E_{i−1}[e^{δA|X_i|}] ≤ K → e^{δA|X_i|} integrable and its conditional expectation given X_1, ..., X_{i−1} is ≤ K almost surely; reason: the finite bound presupposes integrability, and Lean's conditional expectation of a non-integrable function is 0
--   - reading: L a Lipschitz constant, N 'a constant integer' that divides (p. 6) → L ≥ 0 and N ≥ 1; reason: implicit on the page; with L < 0 Lemma 5.2 fails for a deterministic X_i ≡ 1
--   - encoding: X_1, X_2, ... random variables → X_1, ..., X_n measurable; reason: random variables are measurable; only X_1, ..., X_n enter the statement
--   - generalization: the Lipschitz condition 'for i < ℓ' with no upper limit on ℓ → required only for 1 ≤ i < ℓ ≤ n; reason: fewer hypotheses; only these indices enter Δ_1, ..., Δ_n, and the page's hypothesis implies this one
--   - reading: A = 1 + LM/N, where M = O(N), and n ≤ M → M a free natural number with n ≤ M, A written out as 1 + L·M/N; reason: 'M = O(N)' is commentary about the application, not a hypothesis of the inequality
--   - encoding: E_{i−1}[e^{δ|Δ_i|}] ≤ K² 'for every i' → e^{δ|Δ_i|} integrable and the bound almost surely, for 1 ≤ i ≤ n; reason: the finite bound presupposes integrability; Δ_i is defined for 1 ≤ i ≤ n
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), (5.11), p. 11, in the proof of Lemma 5.3 (hypotheses of Lemma 5.3, p. 10)

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_doobIncrement
import Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- (5.11) in the proof of Lemma 5.3 (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 11):
under the hypotheses of Lemma 5.3, for every `i`, `E_{i−1}[e^{δ|Δ_i|}] ≤ K²`, where `Δ_i` is
Doob's martingale increment of `S_n` (p. 9).

**Formalization Note** `A = 1 + L·M/N` is written out. (5.7) is `IsLipschitzInIncrement μ X i ℓ (L / N)`
(conditionally independent copy, almost surely), required for `1 ≤ i < ℓ ≤ n`. The finite MGF
condition is conditional, `E_{i−1}[e^{δA|X_i|}] ≤ K` almost surely with `E_{i−1} =
condExp (natF X (i - 1)) μ`, for `1 ≤ i ≤ n`, together with the integrability of `e^{δA|X_i|}`
(Lean's `condExp` is `0` on a non-integrable function). `X_1, …, X_n` are measurable, `L ≥ 0`,
`N ≥ 1` (the integer of §4.2), `n ≤ M`; `M` is otherwise free ("`M = O(N)`" is commentary).
`Δ_i = doobIncrement μ X n i`; the conclusion includes the integrability of `e^{δ|Δ_i|}`, which
the paper's finite bound presupposes, and is stated for `1 ≤ i ≤ n`. -/
theorem eq_5_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (N M n : ℕ) (hN : 1 ≤ N) (hnM : n ≤ M) (δ L K : ℝ) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hmeas : ∀ j ∈ Finset.Icc 1 n, Measurable (X j))
    (hLip : ∀ i ℓ : ℕ, 1 ≤ i → i < ℓ → ℓ ≤ n → IsLipschitzInIncrement μ X i ℓ (L / N))
    (hMGFint : ∀ i ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|)) μ)
    (hMGF : ∀ i ∈ Finset.Icc 1 n,
      condExp (natF X (i - 1)) μ (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|))
        ≤ᵐ[μ] fun _ => K) :
    ∀ i ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (δ * |doobIncrement μ X n i ω|)) μ ∧
      condExp (natF X (i - 1)) μ (fun ω => Real.exp (δ * |doobIncrement μ X n i ω|))
        ≤ᵐ[μ] fun _ => K ^ 2 := by sorry

end LiuZhangBRW.Concentration
