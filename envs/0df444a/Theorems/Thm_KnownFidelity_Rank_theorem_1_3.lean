-- Prove2me | Theorems.Thm_KnownFidelity_Rank_theorem_1_3
-- name    : KnownFidelity.Rank.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:53:56.799737+00:00
-- url     : https://prove2.me/theorems/ce54aa7a-d9e1-4dd6-a8b1-7c7953b1e983
-- title:
--   Theorem 1.3 — spectral upper and lower bounds on $\mathsf S_\sigma(\varepsilon)$
-- statement:
--   Let $\sigma$ be a known state with positive eigenvalues $\lambda_1\ge\cdots\ge\lambda_r>0$ and let $t_k=\sum_{i>k}\lambda_i$. There are universal constants $c,C>0$ and $k_0\in\mathbb N$ such that, for every known reference $\sigma$ (in any dimension) and $0<\varepsilon<1/2$,
--
--   $$\mathsf S_\sigma(\varepsilon)\ \le\ \Bigg\lceil\frac{C}{\varepsilon^2}\ \min_{\substack{1\le k\le r\\ t_k\le\varepsilon^2/16}}\ k\Big(\sum_{i=1}^k\sqrt{\lambda_i}\Big)^2\Bigg\rceil ,$$
--
--   and, for every $k_0\le k\le r$ with $\varepsilon\le c\sqrt{k\lambda_k}$,
--
--   $$\mathsf S_\sigma(\varepsilon)\ \ge\ \frac{c\,k^3\lambda_k}{\varepsilon^2\log^4(k+1)} .$$
--
--   The upper bound keeps a spectral subspace carrying all but $\varepsilon^2/16$ of the mass; the lower bound embeds the hard instances of Proposition 4.1 into the top $k$ eigenvectors. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: S_σ(ε) ≤ ⌈(C/ε²) min_{k feasible} k(Σ_{i≤k} √λ_i)²⌉ → for every k with 1 ≤ k ≤ r and t_k ≤ ε²/16, S_σ(ε) ≤ ⌈(C/ε²) k(Σ_{i≤k} √λ_i)²⌉; reason: the minimum is over a finite nonempty set (k = r is feasible) and ⌈·⌉ is monotone, so the two forms are equivalent
--   - encoding: λ_1 ≥ ⋯ ≥ λ_r > 0, the positive eigenvalues → eigDesc σ i (Mathlib's sorted eigenvalues₀ at i − 1) for 1 ≤ i ≤ r = rank σ; reason: for a state the first rank σ sorted eigenvalues are exactly the positive ones
--   - encoding: least number of copies S → infimum in ℕ∞ (⊤ when no n works), compared via Nat.ceil cast to ℕ∞ or in ℝ≥0∞; reason: in ℕ the empty infimum is 0, which would make upper bounds trivial
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1.2 and Theorem 1.3, p. 2 (PDF p. 4)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyComplexityUnr
import Definitions.Def_KnownFidelity_Rank_eigDesc

namespace KnownFidelity.Rank

/-- **Theorem 1.3 (Spectral upper and lower bounds).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1.2 and Theorem 1.3, printed p. 2 (PDF p. 4): "Write its positive eigenvalues as
λ₁ ≥ · · · ≥ λ_r > 0 and let t_k = Σ_{i>k} λ_i. Theorem 1.3 (Spectral upper and lower bounds).
There are universal constants c, C > 0 and k₀ ∈ N such that, for every known reference σ and
0 < ε < 1/2, S_σ(ε) ≤ ⌈(C/ε²) min_{1≤k≤r, t_k≤ε²/16} k (Σ_{i=1}^k √λ_i)²⌉. (3) For every
k₀ ≤ k ≤ r with ε ≤ c√(kλ_k), S_σ(ε) ≥ ck³λ_k/(ε² log⁴(k + 1)). (4)"

For every state `σ` on `ℂ^d` of rank `r` (any `d`) and `0 < ε < 1/2`: (3) and (4), with the same
universal `c, C, k₀`.

**Formalization Note.** `λ_i = eigDesc σ i` (the `i`-th largest eigenvalue; for `i ≤ r = rank σ`
these are the positive ones), `t_k = Σ_{k<i≤r} λ_i`, `S_σ(ε) = copyComplexityUnr σ ε`, `log`
natural. (3) is written as "for every `k` with `1 ≤ k ≤ r` and `t_k ≤ ε²/16`,
`S_σ(ε) ≤ ⌈(C/ε²) k (Σ_{i≤k} √λ_i)²⌉`": the minimum is over a finite nonempty set (`k = r` has
`t_r = 0`) and `⌈·⌉` is monotone, so this is equivalent to the printed form. (4) is compared in
`ℝ≥0∞`, and one `c` appears in both places of (4). -/
theorem theorem_1_3 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, ∀ (d : ℕ) (σ : Matrix (Fin d) (Fin d) ℂ),
      QAlgorithms.IsDensityMatrix σ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        (∀ k : ℕ, 1 ≤ k → k ≤ σ.rank → ∑ i ∈ Finset.Ioc k σ.rank, eigDesc σ i ≤ ε ^ 2 / 16 →
          copyComplexityUnr σ ε ≤
            ((⌈C / ε ^ 2 * (k * (∑ i ∈ Finset.Icc 1 k, Real.sqrt (eigDesc σ i)) ^ 2)⌉₊ : ℕ) : ℕ∞)) ∧
        (∀ k : ℕ, k₀ ≤ k → k ≤ σ.rank → ε ≤ c * Real.sqrt (k * eigDesc σ k) →
          ENNReal.ofReal (c * (k : ℝ) ^ 3 * eigDesc σ k / (ε ^ 2 * Real.log (k + 1) ^ 4)) ≤
            (copyComplexityUnr σ ε : ENNReal)) := by sorry

end KnownFidelity.Rank
