-- Prove2me | Theorems.Thm_MagicNumberShellModel_card_oscillatorLevel
-- name    : MagicNumberShellModel.card_oscillatorLevel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T15:51:29.071362+00:00
-- url     : https://prove2.me/theorems/ec54ab50-3d39-4e05-82a4-ea6914d37a94
-- title:
--   Stars and bars: $|L_n| = \binom{n+2}{2}$
-- statement:
--   Let $L_n$ be the set of states of the isotropic three-dimensional harmonic oscillator at energy level $n$, that is, the set of triples $(n_x,n_y,n_z)$ of nonnegative integers with $n_x+n_y+n_z=n$. Then the number of such states is
--
--   $$|L_n| \;=\; \binom{n+2}{2} \;=\; \frac{(n+1)(n+2)}{2}.$$
--
--   This is the stars-and-bars count of the weak $3$-compositions of $n$, and it is the degeneracy of the $n$-th oscillator level before spin is taken into account. It is the single combinatorial input of the whole derivation: every later count is obtained from it by doubling and summing.
--
--   **Formalization Note.** The binomial coefficient is the natural-number $\mathrm{choose}$ function, so the identity is stated without division.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem card_oscillatorLevel (n : ℕ) :
    (oscillatorLevel n).card = (n + 2).choose 2 := by sorry

end MagicNumberShellModel
