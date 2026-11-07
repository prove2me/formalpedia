-- Prove2me | Theorems.Thm_MinSumClust_appendix_A1_bipoint
-- name    : MinSumClust.appendix_A1_bipoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:46:40.205398+00:00
-- url     : https://prove2.me/theorems/9b686d5f-1d0a-4ad6-b2dc-3c56711d7743
-- title:
--   Appendix A.1 — the bound at the end of the binary search of the proof of Theorem 1
-- statement:
--   Let $k_1\le k<k_2\le n$ with $n>0$, $f_2<f_1$, $\varepsilon,w\ge 0$ and $f_1-f_2\le\varepsilon w/n$ (the stopping rule of the binary search). Suppose both final pairs satisfy the guarantee of Theorem 2 with an LMP constant $c$ (the paper's $c=2\times10^7$): $f_1k_1+c_1\le kf_1+c\,\mathrm{opt}$ and $f_2k_2+c_2\le kf_2+c\,\mathrm{opt}$, where $c_i=\mathrm{cost}(\mathcal S_i)$ and $k_i=|\mathcal S_i|$. Then
--
--   $$\frac{k_2-k}{k_2-k_1}\,c_1+\frac{k-k_1}{k_2-k_1}\,c_2\ \le\ \varepsilon w+c\cdot\mathrm{opt},$$
--
--   and if moreover $w\le\mathrm{opt}$ then $\varepsilon w+c\cdot\mathrm{opt}\le(c+\varepsilon)\,\mathrm{opt}$. Applying Theorem 3 to the two final solutions gives Theorem 1.
--
--   Differences from the source:
--
--   - reading: the display for the final two solutions of the binary search → the same inequalities for real numbers satisfying the invariants of the search (k₁ ≤ k < k₂ ≤ n, f₂ < f₁, the stopping rule, and Theorem 2's guarantee for both pairs); reason: these are the facts the display relies on; k₂ ≤ n because 𝒮₂ partitions the n clients
--   - reading: ≤ (2×10⁷ + ε)opt → a second clause under the hypothesis w ≤ opt; reason: A.1: "opt ≥ w > 0"
--   - generalization: the constant 2 × 10⁷ → any constant c; reason: the inequality does not depend on its value; c = 2×10⁷ is the paper's case
--   - generalization: ε > 0 and w > 0 (A.1: "opt ≥ w > 0") → ε ≥ 0 and w ≥ 0; reason: both inequalities still hold at 0; the paper's case ε, w > 0 is included
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Appendix A.1, p.62 (PDF p.64)

import Mathlib

namespace MinSumClust

/-- **The binary-search bound of the proof of Theorem 1**, Appendix A.1, p.62 (PDF p.64).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Appendix A.1, p.62: when the binary search halts with
`f₁ − f₂ ≤ εw/n`, the final pairs `(𝒮₁, f₁)`, `(𝒮₂, f₂)` satisfy
`((k₂−k)/(k₂−k₁)) cost(𝒮₁) + ((k−k₁)/(k₂−k₁)) cost(𝒮₂) ≤ εw + 2×10⁷·opt ≤ (2×10⁷ + ε)·opt`.

Here `c₁ = cost(𝒮₁)`, `c₂ = cost(𝒮₂)`, `k_i = |𝒮_i|`, and the hypotheses are the invariants of the
search: `k₁ ≤ k < k₂ ≤ n`, `f₂ < f₁`, and the guarantee of Theorem 2 for both pairs,
`f_i k_i + c_i ≤ k f_i + c · opt`, with LMP constant `c` (`2 × 10⁷` in the paper).

**Formalization Note.** The display is posed for the real numbers it relates. The second
inequality uses `w ≤ opt` (A.1: "opt ≥ w > 0") and is the second clause. -/
theorem appendix_A1_bipoint (n k k₁ k₂ : ℕ) (f₁ f₂ c₁ c₂ c opt ε w : ℝ) (hn : 0 < n)
    (hk₁ : k₁ ≤ k) (hk₂ : k < k₂) (hk₂n : k₂ ≤ n) (hf : f₂ < f₁)
    (hstop : f₁ - f₂ ≤ ε * w / n) (hε : 0 ≤ ε) (hw : 0 ≤ w)
    (h₁ : f₁ * k₁ + c₁ ≤ k * f₁ + c * opt) (h₂ : f₂ * k₂ + c₂ ≤ k * f₂ + c * opt) :
    ((k₂ : ℝ) - k) / ((k₂ : ℝ) - k₁) * c₁ + ((k : ℝ) - k₁) / ((k₂ : ℝ) - k₁) * c₂ ≤
        ε * w + c * opt ∧
      (w ≤ opt → ε * w + c * opt ≤ (c + ε) * opt) := by sorry

end MinSumClust
