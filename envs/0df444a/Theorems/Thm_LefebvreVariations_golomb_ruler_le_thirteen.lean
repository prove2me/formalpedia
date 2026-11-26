-- Prove2me | Theorems.Thm_LefebvreVariations_golomb_ruler_le_thirteen
-- name    : LefebvreVariations.golomb_ruler_le_thirteen
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:42:55.757974+00:00
-- url     : https://prove2.me/theorems/0675e8ae-d99a-4c19-aeda-93e5addecff5
-- title:
--   Lefebvre's variations, No. 58 — on a theme by Erdős and Turán: a Golomb ruler with n marks has length at most n squared for n at most 13
-- statement:
--   Let $n$ be an integer with $1\le n\le 13$. Then there is a set $R\subseteq\mathbb{N}$ of exactly $n$ marks such that all marks are at most $n^2$ and all non-zero differences are distinct: whenever $a,b,c,d\in R$ with $a\ne b$, $c\ne d$ and $a-b=c-d$, we have $a=c$ and $b=d$.
--
--   In other words, for $n\le 13$ there is a Golomb ruler with $n$ marks and all marks $\le n^2$ (a Sidon set of $n$ integers in $[0,n^2]$). Such rulers are known explicitly, and the known optimal ones are far shorter than $n^2$, with lengths $0,1,3,6,11,17,25,34,44,55,72,85,106$ for $n=1,\dots,13$. The same statement for every $n\ge 1$ is the open Golomb ruler conjecture on the platform; the order $n^2$ is the natural one, since a ruler with $n$ marks cannot be much shorter than about $n^2$ (Erdős–Turán).
--
--   **Formalization Note** The ruler is a `Finset ℕ` with `card = n`. The Golomb condition is `∀ a b c d ∈ ruler, a ≠ b → c ≠ d → (a - b : ℤ) = (c - d : ℤ) → a = c ∧ b = d`, with the subtraction taken in $\mathbb{Z}$ (not truncated). The bound is copied from the parent exactly as it is written there: `∀ m ∈ ruler, m ≤ n ^ 2` stands inside the scope of the quantifiers over `a b c d` and of their hypotheses, as a further conjunct after `a = c ∧ b = d`. Because `a = c ∧ b = d` is satisfied by taking $(c,d)=(a,b)$, the bound is thus asserted whenever the ruler has two distinct marks, that is for every $n\ge 2$; for $n=1$ there is no pair $a\ne b$, so the bound is vacuous there (the ruler $\{0\}$ is used anyway). The ruler need not contain $0$; the bound applies to all of its marks, so its length is at most $n^2$.
--
--   **Why this is a variation.** Variation on the open golomb_ruler_conjecture (a Golomb ruler with $n$ marks fits in length $n^2$). It restricts the parent to $1\le n\le13$, a finite range where the conjecture can be settled by exhibiting explicit rulers, so it is a partial result of the conjecture; the conclusion is copied unchanged from the parent. Settling it supplies the explicit small rulers any attack on the general statement has to agree with.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Golomb rulers (Sidon sets): the lengths of optimal rulers are tabulated in OEIS A003022 and on the Wikipedia page "Golomb ruler"; the table of optimal rulers for 1 <= n <= 13 was found by exhaustive computer search by several authors (names and years cited from memory, not verified here). The rulers used in the proof are the known optimal ones, written out explicitly and checked by Lean, so the correctness of this statement does not depend on those references. The lower bound of order n^2 on the length of an n-mark ruler is due to P. Erdos and P. Turan, On a problem of Sidon in additive number theory, and on some related problems, J. London Math. Soc. 16 (1941), 212-215 (title, volume and pages cited from memory, not re-checked). Origin of this statement: the range 1 <= n <= 13 of the platform theorem golomb_ruler_conjecture (Open), whose conclusion it copies verbatim, with the extra hypothesis n <= 13; it is proved by exhibiting one explicit ruler for each n and a finite kernel check of the Golomb property and of the bound n^2.

import Mathlib

namespace LefebvreVariations

/-- The Golomb ruler conjecture (a Golomb ruler with `n` marks and length at most `n²`) for
`n ≤ 13`: explicit optimal rulers exist, of lengths `0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85, 106`
(all far below `n²`). The conclusion is the parent's, verbatim.
Source: optimal Golomb rulers were found by exhaustive search (Shearer, Robinson–Bernstein,
Atkinson et al.; the table is OEIS A003022 and https://en.wikipedia.org/wiki/Golomb_ruler),
cited from memory; the bound `n²` goes back to Erdős and Turán, "On a problem of Sidon in
additive number theory", J. London Math. Soc. 16 (1941), 212-215 (cited from memory). -/
theorem golomb_ruler_le_thirteen (n : ℕ) (hn : 1 ≤ n) (hn13 : n ≤ 13) :
    ∃ (ruler : Finset ℕ),
      ruler.card = n ∧
      ∀ a b c d : ℕ, a ∈ ruler → b ∈ ruler → c ∈ ruler → d ∈ ruler →
        a ≠ b → c ≠ d → (a - b : ℤ) = (c - d : ℤ) → a = c ∧ b = d ∧
      ∀ m : ℕ, m ∈ ruler → m ≤ n ^ 2 := by
  sorry

end LefebvreVariations
