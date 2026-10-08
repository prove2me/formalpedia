-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_theorem_7_5
-- name    : FuzzyExtractors.EditSketch.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:11.43224+00:00
-- url     : https://prove2.me/theorems/2206edfb-b1d0-41a3-b10d-a1fb7c884182
-- title:
--   Theorem 7.5 — an average-case secure sketch for edit distance with loss $\lceil n/c\rceil\log_2(n-c+1) + (2c-1)t\lceil\log(F^c+1)\rceil$
-- statement:
--   Let $\mathcal F$ be a finite alphabet with $F = |\mathcal F|$ letters, and let $\mathrm{Edit}_{\mathcal F}(n)$ be the strings of length $n$ over $\mathcal F$, with distance the smallest number of character insertions and deletions transforming one string into the other. For all natural numbers $n, c, t$ with $1 \le c \le n$ and every real $m$, there is an average-case
--   $$\Big(\mathrm{Edit}_{\mathcal F}(n),\ m,\ m - \big\lceil \tfrac nc \big\rceil \log_2(n - c + 1) - (2c - 1)\,t\,\big\lceil \log(F^c + 1) \big\rceil,\ t\Big)$$
--   secure sketch.
--
--   The first term of the entropy loss comes from the shingling embedding and its recovery information, the second from PinSketch run on the shingle set over the universe $\mathcal F^c$ embedded into $GF(2^\mu)^*$ with $\mu = \lceil \log(F^c + 1) \rceil$. The parameter $c$ trades the two terms off.
--
--   **Formalization Note.** The paper's statement carries "$0 < \epsilon \le 1$", a parameter that does not occur in the conclusion (a carry-over from Theorem 7.4); it is dropped. $t$ is universally quantified, and the implicit range $1 \le c \le n$ is made explicit. $\lceil \log(F^c + 1) \rceil$ is `Nat.clog 2 (F ^ c + 1)`, the least $\mu$ with $F^c + 1 \le 2^\mu$, and $\lceil n/c \rceil$ is `⌈(n : ℝ) / c⌉₊`. "Efficient" is dropped. The sketch type and the (possibly randomized) procedures are existentially quantified; the edit distance is the published weighted edit distance with cost $1$ per insertion or deletion and $2$ per replacement.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Theorem 7.5, p. 27

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem theorem_7_5 (𝓕 : Type) [Fintype 𝓕] [DecidableEq 𝓕] (n c t : ℕ) (m : ℝ)
    (hc : 1 ≤ c) (hcn : c ≤ n) :
    ∃ (S : Type) (SS : EditSpace 𝓕 n → PMF S) (Rec : EditSpace 𝓕 n → S → PMF (EditSpace 𝓕 n)),
      FuzzyExtractors.Hamming.IsAvgSecureSketch editDis m
        (m - (⌈(n : ℝ) / c⌉₊ : ℝ) * Real.logb 2 ((n : ℝ) - c + 1)
          - (2 * (c : ℝ) - 1) * t * (Nat.clog 2 (Fintype.card 𝓕 ^ c + 1) : ℝ))
        t SS Rec := by sorry

end FuzzyExtractors.EditSketch
