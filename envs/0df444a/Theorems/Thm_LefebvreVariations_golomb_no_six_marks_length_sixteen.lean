-- Prove2me | Theorems.Thm_LefebvreVariations_golomb_no_six_marks_length_sixteen
-- name    : LefebvreVariations.golomb_no_six_marks_length_sixteen
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:02:59.454282+00:00
-- url     : https://prove2.me/theorems/b969bd83-2ca2-51d2-b500-6fa0216fa380
-- title:
--   Lefebvre's variations, No. 113 — on a theme by Paul Erdős and Pál Turán: Golomb rulers with six marks need length at least 17
-- statement:
--   For every finite set $R\subset\mathbb{N}$ with $|R|=6$ whose pairwise differences are distinct (a Golomb ruler), the largest mark satisfies $\max R\ge 17$. Equivalently, there is no Golomb ruler with $6$ marks inside $\{0,1,\dots,16\}$:
--   $$
--   \neg\,\exists R\subset\{0,\dots,16\},\ |R|=6,\ \bigl(a-b=c-d,\ a\ne b,\ c\ne d\ \Rightarrow\ (a,b)=(c,d)\bigr)\ \text{for all }a,b,c,d\in R.
--   $$
--   The optimal length of a Golomb ruler with $6$ marks is exactly $17$ (for instance $\{0,1,4,10,12,17\}$), so this is the sharp lower bound.
--
--   **Formalization Note** The ruler is a `Finset ℕ` of cardinality 6, with all elements at most 16. The distinct-differences condition is the one of the platform's `golomb_ruler_conjecture`: for `a ≠ b`, `c ≠ d` in the ruler, `(a - b : ℤ) = (c - d : ℤ)` forces `a = c` and `b = d`.
--
--   **Why this is a variation.** A companion to the platform's open `golomb_ruler_conjecture` (rulers with n marks and length at most n^2): it shows a fixed small length is too short for 5 (resp. 6) marks, i.e. the optimal length is sharp. It is not a case of the conjecture itself, which stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The optimal length of a Golomb ruler with 6 marks is 17 (OEIS A003022; https://en.wikipedia.org/wiki/Golomb_ruler, tabulated value, not re-checked against the page); the non-existence in [0, 16] was verified here by an exhaustive computer search (and existence at length 17). Parent: the Golomb ruler conjecture on the platform (`golomb_ruler_conjecture`), whose origin is Erdos and Turan, On a problem of Sidon in additive number theory, J. London Math. Soc. 16 (1941) (cited from memory).

import Mathlib

namespace LefebvreVariations

/-- A Golomb ruler with `6` marks needs length at least `17`: no set of `6` naturals inside `[0, 16]` has pairwise distinct differences. Together with the explicit ruler of length `17` this says that the optimal length is `G(6) = 17`. Source: optimal Golomb rulers by exhaustive search, OEIS A003022 (cited from memory). -/
theorem golomb_no_six_marks_length_sixteen :
    ¬ ∃ (ruler : Finset ℕ),
      ruler.card = 6 ∧ (∀ m ∈ ruler, m ≤ 16) ∧
    ∀ a b c d : ℕ, a ∈ ruler → b ∈ ruler → c ∈ ruler → d ∈ ruler →
        a ≠ b → c ≠ d → (a - b : ℤ) = (c - d : ℤ) → a = c ∧ b = d := by
  sorry

end LefebvreVariations
