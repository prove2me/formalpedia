-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_Supplement_low_perimeter_bounds
-- name    : KawasakiSOS.Threshold.Supplement.low_perimeter_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:11:49.17588+00:00
-- url     : https://prove2.me/theorems/d0de4695-3e27-40ba-b679-9a9316b47eb6
-- title:
--   Theorem 1.3: mixing-time bounds for $0<\lambda\le 1$
-- statement:
--   Let $\Omega=\Omega_{n,k}=\{h\in\mathbb Z_{\ge0}^k:\sum_i h(i)=n\}$ be the configurations of $n$ unit squares in $k$ columns arranged on a cycle, let $p(h)$ be the perimeter of $h$, and let $\pi(h)=\lambda^{p(h)}/Z$. Let $\tau(\varepsilon)$ be the mixing time of the lazy Kawasaki chain $\tfrac12(I+P)$, i.e. the least $t$ with $\max_x\|\widehat P^{\,t}(x,\cdot)-\pi\|_{TV}\le\varepsilon$. This theorem covers the low-perimeter regime $0<\lambda\le 1$ (with $\lambda=1$, where $\pi$ is uniform, included).
--
--   There are absolute constants $C_1,C_2>0$ such that for every real $\lambda$ with $0<\lambda\le1$, all integers $2\le k\le n$ and every $\varepsilon\in(0,1)$, the set $\{t:d(t)\le\varepsilon\}$ is nonempty and
--
--   1. (part (a))
--   $$\tau(\varepsilon)\le C_1\,\lambda^{-2}k^2n^2(n+1)^{k-1}\Bigl(n\bigl(1+\log\tfrac1\lambda\bigr)+\log\tfrac1\varepsilon\Bigr);$$
--   2. (part (b))
--   $$\tau(\varepsilon)\le\lambda^{-9}\,(2kn)^{C_2\log_2(2k)}\,\bigl(1+\log(1/\varepsilon)\bigr).$$
--
--   Here $\log$ is the natural logarithm. Part (a) is polynomial in $n$ for fixed $\lambda$ and $k$, with degree growing linearly in $k$; part (b) holds uniformly in $k$ and is quasi-polynomial, improving on (a) once $k$ is large. Together with the $\lambda>1$ bound of Theorem 1.2 they describe the mixing of the chain on both sides of $\lambda=1$; the power $\lambda^{-2}$ in (a) is best possible for fixed $n,k$ up to a factor $\log(1/\lambda)$ (Proposition 8.2).
--
--   **Formalization Note** $\tau$ is an infimum over $\mathbb N$, which Lean sets to $0$ on the empty set, so the statement also asserts that the set of times with $d(t)\le\varepsilon$ is nonempty. $\log_2$ is `Real.logb 2` and $(2kn)^{C_2\log_2(2k)}$ is a real power.
--
--   Differences from the source:
--   - reading: τ(ε) = O(λ^{−2}k²n²(n+1)^{k−1}(n(1 + log(1/λ)) + log(1/ε))) → one constant C₁ > 0 quantified before λ, n, k, ε; reason: the O(·) is read as an absolute constant uniform in every displayed parameter, as for Theorem 1.2 in the base mission; the proof (§8.1, (10)) gives 24 for k ≥ 3 and the paper calls λ^{−2} best possible for fixed n, k, which presupposes uniformity in λ
--   - encoding: an absolute constant C → ∃ C₂ > 0; reason: the right-hand side of (b) is increasing in C (base 2kn ≥ 8, log₂(2k) ≥ 2), so a positive constant exists whenever any constant does
--   - encoding: τ(ε) → τ(ε) together with nonemptiness of {t : d(t) ≤ ε}; reason: Lean's sInf on ℕ is 0 on the empty set; the paper's τ(ε) is a least element that exists
--   - reading: "In particular, for every fixed λ and k ≥ 2 the mixing time is polynomial in n, with degree growing linearly in k" → not stated separately; reason: it follows from the displayed bound of (a) by algebra (for fixed λ, k the bound is a polynomial of degree k + 2 in n times a term linear in n and log(1/ε))
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117f249a36f17a24341fed6a9d149ae947dbdd13558aba49b91103008c1), Theorem 1.3 (a), (b), p. 4 (PDF p. 5); proof §8.1, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_tau
import Definitions.Def_KawasakiSOS_Threshold_mixingSet

namespace KawasakiSOS.Threshold.Supplement

open KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 1.3 (λ ≤ 1), parts (a) and (b), p. 4 (PDF p. 5); proof §8.1, p. 21 (PDF p. 22).

Formalization Notes:
- reading: the `O(·)` of part (a) → one constant `C₁ > 0` quantified before `λ, n, k, ε`, uniform in all of them (the proof gives `24` for `k ≥ 3`, and the paper calls the `λ⁻²` power best possible for fixed `n, k`, which presupposes uniformity in `λ`).
- encoding: "an absolute constant C" of part (b) → `∃ C₂ > 0` before every parameter; requiring `C₂ > 0` loses nothing, since the right-hand side is increasing in `C₂` (base `2kn ≥ 8`, exponent factor `log₂(2k) ≥ 2`).
- encoding: `log` is the natural logarithm `Real.log`; `log₂` is `Real.logb 2`; `(2kn)^{C log₂(2k)}` is a real power.
- encoding: `τ(ε)` is the least `t` with `d(t) ≤ ε` (`sInf` on `ℕ`, `0` on the empty set) → a conjunct asserts that `{t | d(t) ≤ ε}` is nonempty.
- reading: the sentence "In particular, for every fixed λ and k ≥ 2 the mixing time is polynomial in n, with degree growing linearly in k" follows from the displayed bound of (a) and is not stated separately. -/
theorem low_perimeter_bounds :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ (n k : ℕ) [NeZero k], 2 ≤ k → k ≤ n →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          (mixingSet n k lam ε).Nonempty ∧
          (tau n k lam ε : ℝ) ≤ C₁ * (1 / lam ^ 2) * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (k - 1) *
              ((n : ℝ) * (1 + Real.log (1 / lam)) + Real.log (1 / ε)) ∧
          (tau n k lam ε : ℝ) ≤ (1 / lam ^ 9) * (2 * (k : ℝ) * (n : ℝ)) ^ (C₂ * Real.logb 2 (2 * (k : ℝ))) *
              (1 + Real.log (1 / ε)) := by sorry

end KawasakiSOS.Threshold.Supplement
