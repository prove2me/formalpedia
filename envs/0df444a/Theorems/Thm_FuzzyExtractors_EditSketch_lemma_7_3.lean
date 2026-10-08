-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_lemma_7_3
-- name    : FuzzyExtractors.EditSketch.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:30.023691+00:00
-- url     : https://prove2.me/theorems/659e365e-af2d-4aea-b0a3-c7d73c6e88bd
-- title:
--   Lemma 7.3 — $\mathrm{SH}_c$ is an average-case $(t_1, (2c-1)t_1, m_1, m_1 - \lceil n/c\rceil\log_2(n-c+1))$-biometric embedding
-- statement:
--   Let $\mathcal F$ be a finite alphabet and $1 \le c \le n$. Let $\mathrm{SH}_c$ map a string $w \in \mathrm{Edit}_{\mathcal F}(n)$ (length $n$, insertion/deletion distance) to its $c$-shingling, a subset of $\mathcal F^c$, compared in the set-difference metric $\mathrm{SDif}(\mathcal F^c)$. For every $t_1 \in \mathbb N$ and real $m_1$, $\mathrm{SH}_c$ is an average-case
--   $$\Big(t_1,\ t_2 = (2c - 1)t_1,\ m_1,\ m_2 = m_1 - \big\lceil \tfrac nc \big\rceil \log_2(n - c + 1)\Big)$$
--   biometric embedding of $\mathrm{Edit}_{\mathcal F}(n)$ into $\mathrm{SDif}(\mathcal F^c)$. That is:
--
--   1. if $w, w'$ are within $t_1$ insertions and deletions, then $|\mathrm{SH}_c(w) \triangle \mathrm{SH}_c(w')| \le (2c - 1)t_1$;
--   2. for every pair $(W, I)$ with $\tilde{\mathbf H}_\infty(W \mid I) \ge m_1$, we have $\tilde{\mathbf H}_\infty(\mathrm{SH}_c(W) \mid I) \ge m_1 - \lceil n/c \rceil \log_2(n - c + 1)$.
--
--   Shingling turns the edit metric, for which no direct secure sketch is known, into set difference while losing a controlled amount of entropy.
--
--   **Formalization Note.** The paper says "for any $c$"; $1 \le c \le n$ is made explicit (it is needed for $n - c + 1 \ge 1$ and for the shingles to exist). $\lceil n/c \rceil$ is `⌈(n : ℝ) / c⌉₊`. The edit distance is the published weighted edit distance with insertion/deletion cost $1$ and replacement cost $2$; the intermediate strings of an edit sequence may have any length, and `shingles` is defined for every length.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Lemma 7.3, p. 25

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem lemma_7_3 (𝓕 : Type) [Fintype 𝓕] [DecidableEq 𝓕] (n c t₁ : ℕ) (m₁ : ℝ)
    (hc : 1 ≤ c) (hcn : c ≤ n) :
    IsAvgBiometricEmbedding (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2 * c - 1) * t₁) m₁
      (m₁ - (⌈(n : ℝ) / c⌉₊ : ℝ) * Real.logb 2 ((n : ℝ) - c + 1))
      (fun w => shingles c w.1) := by sorry

end FuzzyExtractors.EditSketch
