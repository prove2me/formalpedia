-- Prove2me | Theorems.Thm_MagicSquares_sm3_params_card
-- name    : MagicSquares.sm3_params_card
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T18:23:57.413947+00:00
-- url     : https://prove2.me/theorems/7d09e267-c923-49c2-91f3-76185a464ad4
-- title:
--   Counting the normalized coefficient vectors
-- statement:
--   The number of normalized coefficient vectors —
--   six nonnegative integers summing to $t$ whose odd part $(x,y,z)$ has minimum
--   $0$ — is
--
--   $$\mathrm{sm3Count}(t)=3\binom{t+3}{4}+\binom{t+2}{2}.$$
--
--   **Proof.** Partition the vectors according to the *first* zero among
--   $(x,y,z)$. If $x=0$ the remaining five coordinates are arbitrary nonnegative
--   integers summing to $t$, giving $\binom{t+4}{4}$ vectors. If $x>0$ and $y=0$,
--   subtract $1$ from $x$ and the remaining five coordinates sum to $t-1$, giving
--   $\binom{t+3}{4}$. If $x>0$, $y>0$ and $z=0$, subtract $1$ from each of $x$ and
--   $y$ and the remaining five sum to $t-2$, giving $\binom{t+2}{4}$. Hence
--
--   $$\mathrm{sm3Count}(t)=\binom{t+4}{4}+\binom{t+3}{4}+\binom{t+2}{4}.$$
--
--   Two applications of Pascal's identity collapse this to MacMahon's form:
--   $\binom{t+4}{4}=\binom{t+3}{4}+\binom{t+3}{3}$ and
--   $\binom{t+3}{4}=\binom{t+2}{4}+\binom{t+2}{3}$, so the sum equals
--   $3\binom{t+3}{4}+\bigl(\binom{t+3}{3}-\binom{t+2}{3}\bigr)$, and one more
--   instance of Pascal gives $\binom{t+3}{3}-\binom{t+2}{3}=\binom{t+2}{2}$.
--
--   **Formalization Note** The three counts of five-part compositions come from
--   `comps_card`. Because all arithmetic stays in $\mathbb{N}$, the Pascal steps
--   must be arranged so that no subtraction is truncated.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, Theorem 1.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3
open MagicSquares

namespace MagicSquares

theorem sm3_params_card (t : ℕ) :
    sm3Count t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by sorry

end MagicSquares
