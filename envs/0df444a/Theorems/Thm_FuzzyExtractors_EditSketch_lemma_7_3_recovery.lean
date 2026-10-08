-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_lemma_7_3_recovery
-- name    : FuzzyExtractors.EditSketch.lemma_7_3_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:00.067987+00:00
-- url     : https://prove2.me/theorems/e49e88fa-0b9d-48d5-85f0-02748e8e5eb4
-- title:
--   §7.2 — $\mathrm{SH}_c$ is a biometric embedding with recovery information $g_c$
-- statement:
--   Let $\mathcal F$ be a finite, linearly ordered, nonempty alphabet and $1 \le c \le n$. For every $t_1 \in \mathbb N$, the $c$-shingling map $\mathrm{SH}_c : \mathrm{Edit}_{\mathcal F}(n) \to \mathrm{SDif}(\mathcal F^c)$ is a
--   $$\Big(t_1,\ (2c - 1)t_1,\ \lambda = \big\lceil \tfrac nc \big\rceil \log_2(n - c + 1)\Big)$$
--   biometric embedding with recovery information $g_c$ (Definition 7). That is:
--
--   1. if $w, w'$ are within $t_1$ insertions and deletions, then $|\mathrm{SH}_c(w) \triangle \mathrm{SH}_c(w')| \le (2c - 1)t_1$;
--   2. $g_c$ takes at most $2^\lambda = (n - c + 1)^{\lceil n/c \rceil}$ values;
--   3. $w$ is uniquely determined by $(\mathrm{SH}_c(w), g_c(w))$.
--
--   Here $g_c(w) = (p_1, \dots, p_{\lceil n/c \rceil})$ records, for each of the $\lceil n/c \rceil$ length-$c$ blocks of $w$ (the last two may overlap), the position of that block in the lexicographically sorted shingle set. This is the observation of the "Secure sketches" paragraph of §7.2 that lets Lemma 4.7 be applied to shingling.
--
--   **Formalization Note.** $g_c$ is the concrete function of the proof of Lemma 7.3, with 0-based indices: block $j$ starts at position $\min(jc, n - c)$, and $p_j$ is the number of shingles lexicographically smaller than block $j$ (the paper's index $i$ with $s_j = h_i$, shifted by one). Its values are recorded as natural numbers; the range bound is clause 2. The lexicographic order on $\mathcal F^c$ is `Pi.Lex` from `[LinearOrder 𝓕]`; `[Inhabited 𝓕]` is needed only to write a block down and loses no generality (for an empty alphabet and $n \ge 1$ the space is empty). $1 \le c \le n$ is made explicit.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §7.2, proof of Lemma 7.3 (p. 25) and paragraph "Secure sketches" (p. 26)

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem lemma_7_3_recovery (𝓕 : Type) [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c t₁ : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    IsEmbeddingWithRecovery (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2 * c - 1) * t₁)
      ((⌈(n : ℝ) / c⌉₊ : ℝ) * Real.logb 2 ((n : ℝ) - c + 1))
      (fun w => shingles c w.1) (gc c) := by sorry

end FuzzyExtractors.EditSketch
