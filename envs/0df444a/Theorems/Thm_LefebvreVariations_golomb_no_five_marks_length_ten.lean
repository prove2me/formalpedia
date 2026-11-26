-- Prove2me | Theorems.Thm_LefebvreVariations_golomb_no_five_marks_length_ten
-- name    : LefebvreVariations.golomb_no_five_marks_length_ten
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:02:43.712832+00:00
-- url     : https://prove2.me/theorems/e21150fc-56e8-4879-b29f-cdd484db3c67
-- title:
--   Lefebvre's variations, No. 132 — on a theme by Paul Erdős and Pál Turán: Golomb rulers with five marks need length at least 11
-- statement:
--   For every finite set $R\subset\mathbb{N}$ with $|R|=5$ whose pairwise differences are distinct (a Golomb ruler), the largest mark satisfies $\max R\ge 11$. Equivalently, there is no Golomb ruler with $5$ marks inside $\{0,1,\dots,10\}$:
--   $$
--   \neg\,\exists R\subset\{0,\dots,10\},\ |R|=5,\ \bigl(a-b=c-d,\ a\ne b,\ c\ne d\ \Rightarrow\ (a,b)=(c,d)\bigr)\ \text{for all }a,b,c,d\in R.
--   $$
--   The optimal length of a Golomb ruler with $5$ marks is exactly $11$ (for instance $\{0,1,4,9,11\}$), so this is the sharp lower bound.
--
--   **Formalization Note** The ruler is a `Finset ℕ` of cardinality 5, with all elements at most 10. The distinct-differences condition is the one of the platform's `golomb_ruler_conjecture`: for `a ≠ b`, `c ≠ d` in the ruler, `(a - b : ℤ) = (c - d : ℤ)` forces `a = c` and `b = d`.
--
--   **Why this is a variation.** A companion to the platform's open `golomb_ruler_conjecture` (rulers with n marks and length at most n^2): it shows a fixed small length is too short for 5 (resp. 6) marks, i.e. the optimal length is sharp. It is not a case of the conjecture itself, which stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The optimal length of a Golomb ruler with 5 marks is 11 (OEIS A003022; https://en.wikipedia.org/wiki/Golomb_ruler, tabulated value, not re-checked against the page); the non-existence in [0, 10] was verified here by an exhaustive computer search (and existence at length 11). Parent: the Golomb ruler conjecture on the platform (`golomb_ruler_conjecture`), whose origin is Erdos and Turan, On a problem of Sidon in additive number theory, J. London Math. Soc. 16 (1941) (cited from memory).

import Mathlib

namespace LefebvreVariations

/-- A Golomb ruler with `5` marks needs length at least `11`: no set of `5` naturals inside `[0, 10]` has pairwise distinct differences. Together with the explicit ruler of length `11` this says that the optimal length is `G(5) = 11`. Source: optimal Golomb rulers by exhaustive search, OEIS A003022 (cited from memory). -/
theorem golomb_no_five_marks_length_ten :
    ¬ ∃ (ruler : Finset ℕ),
      ruler.card = 5 ∧ (∀ m ∈ ruler, m ≤ 10) ∧
    ∀ a b c d : ℕ, a ∈ ruler → b ∈ ruler → c ∈ ruler → d ∈ ruler →
        a ≠ b → c ≠ d → (a - b : ℤ) = (c - d : ℤ) → a = c ∧ b = d := by
  sorry

end LefebvreVariations
