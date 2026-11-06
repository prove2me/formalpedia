-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_lemma_5_3
-- name    : LiuZhangBRW.Concentration.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:17.315228+00:00
-- url     : https://prove2.me/theorems/95eca182-f1aa-43b8-9b28-de7a4b0d7456
-- title:
--   Lemma 5.3 — $\Pr(|S_n-\mathbb ES_n|\ge\lambda)\le2\exp(-\min\{\frac{\delta^2}{4K^2}\frac{\lambda^2}n,\frac{\delta\lambda}2\})$
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
--   Then for every $\lambda$,
--   $$
--   \Pr\bigl(|S_n-\mathbb ES_n|\ge\lambda\bigr)\le2\exp\Bigl(-\min\Bigl\{\frac{\delta^2}{4K^2}\cdot\frac{\lambda^2}{n},\ \frac{\delta\lambda}{2}\Bigr\}\Bigr).\tag{5.8}
--   $$
--
--   This is the paper's concentration inequality for dependent, unbounded increments: neither independence, nor the martingale-difference property, nor bounded increments is assumed.
--
--   **Formalization Note** $\Pr$ is the probability of the event under the given measure and $\mathbb ES_n$ the integral of $S_n$. The Lipschitz condition is `IsLipschitzInIncrement μ X i ℓ (L / N)`. The footnote "the lemma holds for $n=\Theta(M)$" is not part of the statement.
--
--   Differences from the source:
--   - reading: (5.5)/(5.7)/(6.9) with X′_i a conditionally independent copy of X_i given X_1, ..., X_{i−1} → IsLipschitzInIncrement: a version g of E_i X_ℓ as a function of (past, X_i) satisfies |g(p,x) − g(p,x′)| ≤ (L/N)|x − x′| for almost every past p and almost every pair (x, x′) drawn from the product of the conditional law of X_i given p with itself; reason: this is how the proof of Lemma 5.2 (pp. 9–10) uses the condition; demanding the bound for every x, x′ of one version would be a stronger hypothesis
--   - encoding: E_{i−1}[e^{δA|X_i|}] ≤ K → e^{δA|X_i|} integrable and its conditional expectation given X_1, ..., X_{i−1} is ≤ K almost surely; reason: the finite bound presupposes integrability, and Lean's conditional expectation of a non-integrable function is 0
--   - reading: L a Lipschitz constant, N 'a constant integer' that divides (p. 6) → L ≥ 0 and N ≥ 1; reason: implicit on the page; with L < 0 Lemma 5.2 fails for a deterministic X_i ≡ 1
--   - encoding: X_1, X_2, ... random variables → X_1, ..., X_n measurable; reason: random variables are measurable; only X_1, ..., X_n enter the statement
--   - generalization: the Lipschitz condition 'for i < ℓ' with no upper limit on ℓ → required only for 1 ≤ i < ℓ ≤ n; reason: fewer hypotheses; only these indices enter Δ_1, ..., Δ_n, and the page's hypothesis implies this one
--   - reading: A = 1 + LM/N, where M = O(N), and n ≤ M → M a free natural number with n ≤ M, A written out as 1 + L·M/N; reason: 'M = O(N)' is commentary about the application, not a hypothesis of the inequality
--   - generalization: λ (no sign printed) → every real λ; reason: covers every λ > 0; for λ ≤ 0 the right side is at least 2
--   - encoding: Pr(|S_n − ES_n| ≥ λ) → μ.real {ω | λ ≤ |S_n(ω) − ∫ S_n dμ|}; at n = 0, λ²/0 = 0 in Lean; reason: Lean convention; at n = 0, S_0 = 0 and the bound is 2, so no instance changes
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Lemma 5.3, (5.7)–(5.8), p. 10

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_S
import Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Lemma 5.3 (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 10). Let `A = 1 + LM/N`.
If the Lipschitz condition (5.7) `|E_{i−1}(X_ℓ | X_i) − E_{i−1}(X_ℓ | X′_i)| ≤ L|X_i − X′_i|/N`
(`i < ℓ`) holds and `E_{i−1}[e^{δA|X_i|}] ≤ K` (finite MGF) for a constant `δ > 0`,
`i = 1, 2, …, n`, then for `n ≤ M`,
(5.8) `Pr(|S_n − ES_n| ≥ λ) ≤ 2 exp(−min{δ²/(4K²) · λ²/n, δλ/2})`.

**Formalization Note** `A = 1 + L·M/N` is written out. (5.7) is `IsLipschitzInIncrement μ X i ℓ (L / N)`
(conditionally independent copy, almost surely), required for `1 ≤ i < ℓ ≤ n`. The finite MGF
condition is conditional, `E_{i−1}[e^{δA|X_i|}] ≤ K` almost surely with `E_{i−1} =
condExp (natF X (i - 1)) μ`, for `1 ≤ i ≤ n`, together with the integrability of `e^{δA|X_i|}`
(Lean's `condExp` is `0` on a non-integrable function). `X_1, …, X_n` are measurable, `L ≥ 0`,
`N ≥ 1` (the integer of §4.2), `n ≤ M`; `M` is otherwise free ("`M = O(N)`" is commentary).
The bound is stated for every real `λ` (the page prints no sign; for `λ ≤ 0` the right side is
at least `2`). `Pr` is `μ.real`, `ES_n` the Bochner integral under `μ`; at `n = 0`, `λ²/0 = 0`
in Lean, and the claim still holds. -/
theorem lemma_5_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (N M n : ℕ) (hN : 1 ≤ N) (hnM : n ≤ M) (δ L K : ℝ) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hmeas : ∀ j ∈ Finset.Icc 1 n, Measurable (X j))
    (hLip : ∀ i ℓ : ℕ, 1 ≤ i → i < ℓ → ℓ ≤ n → IsLipschitzInIncrement μ X i ℓ (L / N))
    (hMGFint : ∀ i ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|)) μ)
    (hMGF : ∀ i ∈ Finset.Icc 1 n,
      condExp (natF X (i - 1)) μ (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|))
        ≤ᵐ[μ] fun _ => K)
    (lam : ℝ) :
    μ.real {ω | lam ≤ |S X n ω - ∫ ω', S X n ω' ∂μ|} ≤
      2 * Real.exp (-(min (δ ^ 2 / (4 * K ^ 2) * (lam ^ 2 / n)) (δ * lam / 2))) := by sorry

end LiuZhangBRW.Concentration
