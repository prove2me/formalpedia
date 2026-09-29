-- Prove2me | Theorems.Thm_MagicNumberShellModel_cumulativeCapacity_eq
-- name    : MagicNumberShellModel.cumulativeCapacity_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:24:38.947467+00:00
-- url     : https://prove2.me/theorems/f05d63c9-ef06-46d1-aae0-6ee6ce986ed6
-- title:
--   Closed form for the shell-filling count: $S_N = 2\binom{N+2}{3}$
-- statement:
--   Let $C_n = 2\,|L_n|$ be the capacity of the oscillator shell at level $n$ and let
--
--   $$S_N \;=\; \sum_{n<N} C_n$$
--
--   be the number of nucleons needed to fill every shell of level strictly below $N$. Then for every $N \ge 0$
--
--   $$S_N \;=\; 2\binom{N+2}{3} \;=\; \frac{N(N+1)(N+2)}{3}.$$
--
--   The identity turns the shell-closure numbers from a running sum into a closed-form cubic, which is what makes global statements about the predicted sequence — such as which integers never occur in it — accessible.
--
--   **Formalization Note.** The statement is written as $2\binom{N+2}{3}$ rather than $N(N+1)(N+2)/3$ so that no natural-number division occurs. The case $N=0$ is included: both sides are $0$.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem cumulativeCapacity_eq (N : ℕ) :
    cumulativeCapacity N = 2 * (N + 2).choose 3 := by sorry

end MagicNumberShellModel
