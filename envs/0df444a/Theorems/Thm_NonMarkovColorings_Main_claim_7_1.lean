-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_claim_7_1
-- name    : NonMarkovColorings.Main.claim_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:42.991906+00:00
-- url     : https://prove2.me/theorems/d277842f-f56c-405c-9186-60d9bad35e9f
-- title:
--   Claim 7.1 — rank matching of two 0/1 lists with close prefix counts: at most $(\varepsilon+\varepsilon^{1/2})m$ bad indices
-- statement:
--   Let $1\ge p_1\ge\dots\ge p_m\ge0$ and $X_i,Y_i\in\{0,1\}$ satisfy $\big|\sum_{i\le j}(X_i-Y_i)\big|\le\varepsilon m$ whenever $j=m$ or $p_j>p_{j+1}$. Define $\mathrm{index}(R)=\min\{j:\sum_{i\le j}Y_i\ge R\}$ when this set is nonempty. For each $j$ with $X_j=1$ let $R=\sum_{i\le j}X_i$. Then at most $(\varepsilon+\varepsilon^{1/2})m$ such indices $j$ have $\mathrm{index}(R)$ undefined or satisfy
--   $$|p_j-p_{\mathrm{index}(R)}|>\varepsilon^{1/2}.$$
--   A deterministic order-statistics fact used to compare the blocking and unblocked neighbours in §7.
--
--   **Formalization Note.** Indices are $1,\dots,m$; $p,X,Y$ are functions on $\mathbb N$ used on $[1,m]$; $\varepsilon^{1/2}$ is `Real.sqrt ε`.
--
--   Differences from the source:
--   - encoding: ε ≥ 0 implicit (ε^{1/2}) → ε : ℝ arbitrary, ε^{1/2} = Real.sqrt ε; reason: for ε < 0 and m ≥ 1 the hypothesis at j = m is unsatisfiable, and m = 0 gives 0 ≤ 0; no instance changes
--   - encoding: lists p_1..p_m, X_1..X_m, Y_1..Y_m → functions ℕ → ℝ, ℕ → ℕ constrained on Finset.Icc 1 m; index ranges over [1, m]; reason: 1-based indices as in the paper
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 56, Claim 7.1

import Mathlib

namespace NonMarkovColorings.Main

/-- Claim 7.1. Let `1 ≥ p_1 ≥ ⋯ ≥ p_m ≥ 0` and `X_i, Y_i ∈ {0, 1}` with
`|Σ_{i ≤ j} (X_i − Y_i)| ≤ ε m` whenever `j = m` or `p_j > p_{j+1}`. With
`index(R) = min{j : Σ_{i ≤ j} Y_i ≥ R}`, at most `(ε + ε^{1/2}) m` indices `j` with `X_j = 1`
have, for `R = Σ_{i ≤ j} X_i`, `index(R)` undefined or `|p_j − p_{index(R)}| > ε^{1/2}`.
Indices run over `1, …, m`. -/
theorem claim_7_1 (m : ℕ) (ε : ℝ) (p : ℕ → ℝ) (X Y : ℕ → ℕ)
    (hp1 : ∀ i ∈ Finset.Icc 1 m, p i ≤ 1) (hp0 : ∀ i ∈ Finset.Icc 1 m, 0 ≤ p i)
    (hmono : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, i ≤ j → p j ≤ p i)
    (hX : ∀ i ∈ Finset.Icc 1 m, X i = 0 ∨ X i = 1)
    (hY : ∀ i ∈ Finset.Icc 1 m, Y i = 0 ∨ Y i = 1)
    (hsum : ∀ j ∈ Finset.Icc 1 m, (j = m ∨ p (j + 1) < p j) →
      |∑ i ∈ Finset.Icc 1 j, ((X i : ℝ) - (Y i : ℝ))| ≤ ε * m) :
    (((Finset.Icc 1 m).filter fun j => X j = 1 ∧
        let S := (Finset.Icc 1 m).filter fun j' =>
          ∑ i ∈ Finset.Icc 1 j, X i ≤ ∑ i ∈ Finset.Icc 1 j', Y i
        S = ∅ ∨ ∃ h : S.Nonempty, Real.sqrt ε < |p j - p (S.min' h)|).card : ℝ) ≤
      (ε + Real.sqrt ε) * m := by sorry

end NonMarkovColorings.Main
