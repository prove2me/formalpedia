-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_corollary_6_1
-- name    : LiuZhangBRW.Concentration.corollary_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:19.504641+00:00
-- url     : https://prove2.me/theorems/dab13269-ff99-46b2-841a-8de6c11602f1
-- title:
--   Corollary 6.1 — under $P^{(M)}$, $\Pr(|S_n-\mathbb ES_n|\ge\lambda)\le2\exp(-c\lambda^2/n)$, $c=\min\{\frac{\delta^2}{4K^2},\frac{\delta}{4C}\}$
-- statement:
--   Let a branching random walk be given with starting point $u_0$, scaling integer $N\ge1$, birth rates $a_i\ge0$ and displacement laws $p_i(\cdot\mid u)$, and let $X_i$ be the displacement at generation $i$ of a lineage, $u_i=u_0+(X_1+\dots+X_i)/N$, $S_n=X_1+\dots+X_n$. Let $n\le M$ and assume the population measure $P^{(M)}$ of (6.5) is well defined. Write $\Pr$, $\mathbb E$ and $\mathbb E^{(M)}_{i-1}$ for probability, expectation and conditional expectation given $X_1,\dots,X_{i-1}$ under $P^{(M)}$. Let $\delta>0$, $L\ge0$, $K\in\mathbb R$ and $A=1+LM/N$. Assume
--
--   1. (6.9) $\bigl|\mathbb E^{(M)}_{i-1}(X_\ell\mid X_i)-\mathbb E^{(M)}_{i-1}(X_\ell\mid X_i')\bigr|\le L|X_i-X_i'|/N$ for $1\le i<\ell\le n$, with $X_i'$ a conditionally independent copy of $X_i$ given $X_1,\dots,X_{i-1}$ under $P^{(M)}$;
--   2. (6.10) $e^{\delta A|X_i|}$ is $P^{(M)}$-integrable and $\mathbb E^{(M)}_{i-1}\bigl(e^{\delta A|X_i|}\bigr)\le K$ almost surely, for $1\le i\le n$.
--   3. $|S_n|<Cn$ $P^{(M)}$-almost surely, for a constant $C>0$.
--
--   Then for every $\lambda>0$,
--   $$
--   \Pr\bigl(|S_n-\mathbb ES_n|\ge\lambda\bigr)\le2\exp\Bigl(-c\,\frac{\lambda^2}{n}\Bigr),\qquad c=\min\Bigl\{\frac{\delta^2}{4K^2},\frac{\delta}{4C}\Bigr\}.\tag{6.12}
--   $$
--
--   This is the paper's concentration inequality for branching random walks: the population-weighted sum $S_n$ has sub-Gaussian tails with an explicit constant, without independence, martingale differences or bounded increments.
--
--   **Formalization Note** $P^{(M)}$ is `B.popMeasure M`, assumed to be a probability measure (equivalently, its normalizer lies in $(0,\infty)$); the $X_i$ are the coordinates `BRWModel.coord i`. (6.9) is `IsLipschitzInIncrement (B.popMeasure M) coord i ℓ (L / N)`. The hypothesis $|S_n|<Cn$ cannot hold at $n=0$, as on the page. Theorem 6.2, the informal "smooth" version, is not this statement.
--
--   Differences from the source:
--   - reading: Pr and E in Lemma 6.1 / Corollary 6.1 ('where E(S_n) is given by (6.5)'), and E^(M)_{i−1} → the population measure P^(M) = B.popMeasure M of (6.5), and the conditional expectation under P^(M) given X_1, ..., X_{i−1}; reason: (6.3), p. 21 names the population tail as the quantity of interest and p. 24 cites (6.5); eq_6_6_iterated_expectation shows that the ratio (6.6) is a version of this conditional expectation
--   - encoding: (6.5), a ratio with denominator ∫ ∏ a_j dP → IsProbabilityMeasure (B.popMeasure M), equivalent to 0 < normalizer < ∞; reason: (6.5) is undefined when the normalizer is 0 or ∞; the equivalence is proved in the verification file
--   - generalization: displacement densities p_i(x | u_{i−1}) → Markov kernels step i : ℝ → probability measures on ℝ; reason: every density defines a kernel
--   - reading: (5.5)/(5.7)/(6.9) with X′_i a conditionally independent copy of X_i given X_1, ..., X_{i−1} → IsLipschitzInIncrement: a version g of E_i X_ℓ as a function of (past, X_i) satisfies |g(p,x) − g(p,x′)| ≤ (L/N)|x − x′| for almost every past p and almost every pair (x, x′) drawn from the product of the conditional law of X_i given p with itself; reason: this is how the proof of Lemma 5.2 (pp. 9–10) uses the condition; demanding the bound for every x, x′ of one version would be a stronger hypothesis
--   - encoding: E_{i−1}[e^{δA|X_i|}] ≤ K → e^{δA|X_i|} integrable and its conditional expectation given X_1, ..., X_{i−1} is ≤ K almost surely; reason: the finite bound presupposes integrability, and Lean's conditional expectation of a non-integrable function is 0
--   - reading: L a Lipschitz constant, N 'a constant integer' that divides (p. 6) → L ≥ 0 and N ≥ 1; reason: implicit on the page; with L < 0 Lemma 5.2 fails for a deterministic X_i ≡ 1
--   - generalization: (6.9) for i < ℓ and (6.10) for i = 1, 2, ... → (6.9) for 1 ≤ i < ℓ ≤ n and (6.10) for 1 ≤ i ≤ n; reason: fewer hypotheses; only these indices enter S_n, and the page's hypotheses imply these
--   - reading: A = 1 + LM/N, where M = O(N), and n ≤ M → M a free natural number with n ≤ M, A written out as 1 + L·M/N; reason: 'M = O(N)' is commentary about the application, not a hypothesis of the inequality
--   - generalization: |S_n| < Cn → |S_n| < Cn almost surely; reason: a sure bound implies the almost-sure one
--   - encoding: Pr(|S_n − ES_n| ≥ λ) → μ.real {ω | λ ≤ |S_n(ω) − ∫ S_n dμ|}; at n = 0, λ²/0 = 0 in Lean; reason: Lean convention; at n = 0, S_0 = 0 and the bound is 2, so no instance changes
--   - encoding: the lineage (X_1, ..., X_M) with law (6.5) on ℝ^M → the coordinates BRWModel.coord of the path space ℕ → ℝ under B.popMeasure M (coordinate 0 ≡ 0, coordinates after M following the unweighted random walk); reason: the statement involves only X_1, ..., X_n with n ≤ M, whose joint law under B.popMeasure M is (6.5)'s
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Corollary 6.1, (6.12), p. 24 (with the hypotheses of Lemma 6.1)

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_S
import Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel_popMeasure

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Corollary 6.1 (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 24). Under the hypotheses
of Lemma 6.1, suppose in addition that `|S_n| < Cn` for some constant `C > 0`. Then for every
`λ > 0`, (6.12) `Pr(|S_n − ES_n| ≥ λ) ≤ 2 exp(−cλ²/n)` with `c = min{δ²/(4K²), δ/(4C)}`.

**Formalization Note** `Pr` and `E` are the population measure `P^(M) = B.popMeasure M` of (6.5)
(p. 24: "where `E(S_n)` is given by (6.5)"), assumed to be a probability measure, which holds
exactly when its normalizer is in `(0, ∞)`, i.e. when (6.5) is defined. The `X_i` are the
coordinates of the lineage. `E_{i−1}^(M)` is the conditional expectation under `P^(M)` given
`X_1, …, X_{i−1}`; the theorem `eq_6_6_iterated_expectation` shows that the ratio (6.6) is a
version of it. (6.9) is `IsLipschitzInIncrement (B.popMeasure M) coord i ℓ (L / N)`
(conditionally independent copy, almost surely), for `1 ≤ i < ℓ ≤ n`; (6.10) is conditional, with
the integrability of `e^{δA|X_i|}`, for `1 ≤ i ≤ n` (the page writes `i = 1, 2, …`).
`A = 1 + L·M/N` is written out, `L ≥ 0`, `N ≥ 1`, `n ≤ M`, `M` otherwise free. Displacement laws
are Markov kernels (generalizing densities).
`|S_n| < Cn` is assumed `P^(M)`-almost surely; at `n = 0` it cannot hold, as on the page. -/
theorem corollary_6_1
    (B : BRWModel) (hN : 1 ≤ B.N) (M n : ℕ) (hnM : n ≤ M)
    [IsProbabilityMeasure (B.popMeasure M)] (δ L K : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hLip : ∀ i ℓ : ℕ, 1 ≤ i → i < ℓ → ℓ ≤ n →
      IsLipschitzInIncrement (B.popMeasure M) BRWModel.coord i ℓ (L / B.N))
    (hMGFint : ∀ i ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / B.N) * |BRWModel.coord i ω|))
        (B.popMeasure M))
    (hMGF : ∀ i ∈ Finset.Icc 1 n,
      condExp (natF BRWModel.coord (i - 1)) (B.popMeasure M)
          (fun ω => Real.exp (δ * (1 + L * (M : ℝ) / B.N) * |BRWModel.coord i ω|))
        ≤ᵐ[B.popMeasure M] fun _ => K)
    (C : ℝ) (hC : 0 < C) (hS : ∀ᵐ ω ∂(B.popMeasure M), |S BRWModel.coord n ω| < C * n)
    (lam : ℝ) (hlam : 0 < lam) :
    (B.popMeasure M).real
        {ω | lam ≤ |S BRWModel.coord n ω - ∫ ω', S BRWModel.coord n ω' ∂(B.popMeasure M)|} ≤
      2 * Real.exp (-(min (δ ^ 2 / (4 * K ^ 2)) (δ / (4 * C))) * lam ^ 2 / n) := by sorry

end LiuZhangBRW.Concentration
