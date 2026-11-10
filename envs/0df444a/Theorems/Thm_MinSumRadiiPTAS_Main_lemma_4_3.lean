-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_4_3
-- name    : MinSumRadiiPTAS.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:05:58.688205+00:00
-- url     : https://prove2.me/theorems/49fa0a7e-52d3-4d3e-9feb-bb8886e43a68
-- title:
--   Lemma 4.3 — random thresholds: $E_\sigma[\mathrm{lo}_B/r_B] \le 2/L$ and $E_\sigma[r_B/\mathrm{hi}_B] \le 2/L$
-- statement:
--   **Lemma 4.3** (p. 10). For the thresholds of Algorithm 1 with multiplier $L$, opening cost $\lambda > 0$ and any target, and for any radius $r_B$ with $0 < r_B \le a_t$ (for every value of $\sigma$), with $\sigma$ uniform on $\{0, \dots, L-1\}$:
--   $$\mathbb E_\sigma\Big[\frac{\mathrm{lo}_B}{r_B}\Big] \le \frac 2L \quad\text{and}\quad \mathbb E_\sigma\Big[\frac{r_B}{\mathrm{hi}_B}\Big] \le \frac 2L.$$
--
--   Differences from the source:
--   - generalization: L = ⌈e^{1200}/ε⌉ (§4) or ⌈e^{7100}/ε⌉ (§6.2), target ⌈10k/ε⌉ (§4) or 3R (§6.2) → any integer L ≥ 1 and any real target; reason: the proof uses only L ≥ 1 and λ > 0; the statement specializes to both of the paper's settings
--   - reading: "for any ball B with 0 < r_B ≤ a_t" (a_t depends on the random σ) → 0 < r_B and r_B ≤ a_{t(σ)} for every σ ∈ {0, …, L−1}; reason: a hypothesis of an expectation over σ must hold for every σ; it holds whenever r_B ≤ target
--   - encoding: a ball B with radius r_B; E_σ → the radius r alone; the average (1/L) Σ_{σ<L}; reason: lo_B, hi_B depend on B only through r_B; σ is uniform on a finite set
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §4.1, Lemma 4.3, p. 10 (Algorithm 1 pp. 9–10)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Partition

namespace MinSumRadiiPTAS.Main

/-- **Lemma 4.3** (p. 10): for the thresholds of Algorithm 1 with multiplier `L ≥ 1`, opening cost
`λ > 0` and target `target`, and a ball of radius `r_B` with `0 < r_B ≤ a_t` (for every value of
`σ`), the averages over `σ` uniform on `{0, …, L−1}` satisfy `E_σ[lo_B/r_B] ≤ 2/L` and
`E_σ[r_B/hi_B] ≤ 2/L`. -/
theorem lemma_4_3 (L : ℕ) (hL : 1 ≤ L) (lam target r : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hrt : ∀ σ < L, r ≤ thr lam L σ (thrTop lam target L σ)) :
    (1 / (L : ℝ)) * ∑ σ ∈ Finset.range L, loThr lam target L σ r / r ≤ 2 / (L : ℝ) ∧
      (1 / (L : ℝ)) * ∑ σ ∈ Finset.range L, r / hiThr lam target L σ r ≤ 2 / (L : ℝ) := by sorry

end MinSumRadiiPTAS.Main
