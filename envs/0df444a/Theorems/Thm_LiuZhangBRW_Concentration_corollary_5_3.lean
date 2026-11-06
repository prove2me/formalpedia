-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_corollary_5_3
-- name    : LiuZhangBRW.Concentration.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:09.19717+00:00
-- url     : https://prove2.me/theorems/31d9be44-3c2b-4d38-b0da-f7071c4c7d88
-- title:
--   Corollary 5.3 — if also $|S_n|<Cn$, then $\Pr(|S_n-\mathbb ES_n|\ge\lambda)\le2\exp(-c\lambda^2/n)$, $c=\min\{\frac{\delta^2}{4K^2},\frac{\delta}{4C}\}$
-- statement:
--   Let $X_1,X_2,\dots$ be real random variables on a probability space, measurable for $1\le i\le n$, with $\mathbb E_i=\mathbb E(\cdot\mid X_1,\dots,X_i)$. Let $N\ge1$, $n\le M$, $\delta>0$, $L\ge0$, $K\in\mathbb R$ and
--   $$
--   A=1+L\,\frac MN .
--   $$
--   Assume
--
--   1. the Lipschitz condition (5.7): $\bigl|\mathbb E_{i-1}(X_\ell\mid X_i)-\mathbb E_{i-1}(X_\ell\mid X_i')\bigr|\le L|X_i-X_i'|/N$ for $1\le i<\ell\le n$, with $X_i'$ a conditionally independent copy of $X_i$ given $X_1,\dots,X_{i-1}$;
--   2. the finite MGF condition: $e^{\delta A|X_i|}$ is integrable and $\mathbb E_{i-1}\bigl[e^{\delta A|X_i|}\bigr]\le K$ almost surely, for $1\le i\le n$.
--   3. $|S_n|<Cn$ almost surely, for a constant $C>0$.
--
--   Then for every $\lambda>0$,
--   $$
--   \Pr\bigl(|S_n-\mathbb ES_n|\ge\lambda\bigr)\le2\exp\Bigl(-c\,\frac{\lambda^2}{n}\Bigr),\qquad c=\min\Bigl\{\frac{\delta^2}{4K^2},\frac{\delta}{4C}\Bigr\}.\tag{5.9}
--   $$
--
--   This is the sub-Gaussian tail bound that the paper calls a "concentration inequality" from here on.
--
--   **Formalization Note** As on the page, the hypothesis $|S_n|<Cn$ cannot hold at $n=0$. The Lipschitz condition is `IsLipschitzInIncrement μ X i ℓ (L / N)`.
--
--   Differences from the source:
--   - reading: (5.5)/(5.7)/(6.9) with X′_i a conditionally independent copy of X_i given X_1, ..., X_{i−1} → IsLipschitzInIncrement: a version g of E_i X_ℓ as a function of (past, X_i) satisfies |g(p,x) − g(p,x′)| ≤ (L/N)|x − x′| for almost every past p and almost every pair (x, x′) drawn from the product of the conditional law of X_i given p with itself; reason: this is how the proof of Lemma 5.2 (pp. 9–10) uses the condition; demanding the bound for every x, x′ of one version would be a stronger hypothesis
--   - encoding: E_{i−1}[e^{δA|X_i|}] ≤ K → e^{δA|X_i|} integrable and its conditional expectation given X_1, ..., X_{i−1} is ≤ K almost surely; reason: the finite bound presupposes integrability, and Lean's conditional expectation of a non-integrable function is 0
--   - reading: L a Lipschitz constant, N 'a constant integer' that divides (p. 6) → L ≥ 0 and N ≥ 1; reason: implicit on the page; with L < 0 Lemma 5.2 fails for a deterministic X_i ≡ 1
--   - encoding: X_1, X_2, ... random variables → X_1, ..., X_n measurable; reason: random variables are measurable; only X_1, ..., X_n enter the statement
--   - generalization: the Lipschitz condition 'for i < ℓ' with no upper limit on ℓ → required only for 1 ≤ i < ℓ ≤ n; reason: fewer hypotheses; only these indices enter Δ_1, ..., Δ_n, and the page's hypothesis implies this one
--   - reading: A = 1 + LM/N, where M = O(N), and n ≤ M → M a free natural number with n ≤ M, A written out as 1 + L·M/N; reason: 'M = O(N)' is commentary about the application, not a hypothesis of the inequality
--   - generalization: |S_n| < Cn → |S_n| < Cn almost surely; reason: a sure bound implies the almost-sure one
--   - encoding: Pr(|S_n − ES_n| ≥ λ) → μ.real {ω | λ ≤ |S_n(ω) − ∫ S_n dμ|}; at n = 0, λ²/0 = 0 in Lean; reason: Lean convention; at n = 0, S_0 = 0 and the bound is 2, so no instance changes
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Corollary 5.3, (5.9), p. 10 (with the hypotheses of Lemma 5.3)

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_S
import Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Corollary 5.3 (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 10). Under the
hypotheses of Lemma 5.3, suppose in addition that `|S_n| < Cn` for some constant `C > 0`. Then
for every `λ > 0`, (5.9) `Pr(|S_n − ES_n| ≥ λ) ≤ 2 exp(−cλ²/n)` with
`c = min{δ²/(4K²), δ/(4C)}`.

**Formalization Note** `A = 1 + L·M/N` is written out. (5.7) is `IsLipschitzInIncrement μ X i ℓ (L / N)`
(conditionally independent copy, almost surely), required for `1 ≤ i < ℓ ≤ n`. The finite MGF
condition is conditional, `E_{i−1}[e^{δA|X_i|}] ≤ K` almost surely with `E_{i−1} =
condExp (natF X (i - 1)) μ`, for `1 ≤ i ≤ n`, together with the integrability of `e^{δA|X_i|}`
(Lean's `condExp` is `0` on a non-integrable function). `X_1, …, X_n` are measurable, `L ≥ 0`,
`N ≥ 1` (the integer of §4.2), `n ≤ M`; `M` is otherwise free ("`M = O(N)`" is commentary).
`|S_n| < Cn` is assumed almost surely. At `n = 0` it cannot hold, as on the page. -/
theorem corollary_5_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (N M n : ℕ) (hN : 1 ≤ N) (hnM : n ≤ M) (δ L K : ℝ) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hmeas : ∀ j ∈ Finset.Icc 1 n, Measurable (X j))
    (hLip : ∀ i ℓ : ℕ, 1 ≤ i → i < ℓ → ℓ ≤ n → IsLipschitzInIncrement μ X i ℓ (L / N))
    (hMGFint : ∀ i ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|)) μ)
    (hMGF : ∀ i ∈ Finset.Icc 1 n,
      condExp (natF X (i - 1)) μ (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / N) * |X i ω|))
        ≤ᵐ[μ] fun _ => K)
    (C : ℝ) (hC : 0 < C) (hS : ∀ᵐ ω ∂μ, |S X n ω| < C * n) (lam : ℝ) (hlam : 0 < lam) :
    μ.real {ω | lam ≤ |S X n ω - ∫ ω', S X n ω' ∂μ|} ≤
      2 * Real.exp (-(min (δ ^ 2 / (4 * K ^ 2)) (δ / (4 * C))) * lam ^ 2 / n) := by sorry

end LiuZhangBRW.Concentration
