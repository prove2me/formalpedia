-- Prove2me | Theorems.Thm_MagicNumberShellModel_cumulativeCapacity_first_values
-- name    : MagicNumberShellModel.cumulativeCapacity_first_values
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:38:08.882299+00:00
-- url     : https://prove2.me/theorems/b8708a83-a906-4608-972c-c72cf044b73c
-- title:
--   Predicted shell closures: $2, 8, 20, 40$
-- statement:
--   With $S_N = \sum_{n<N} C_n$ the number of nucleons filling all oscillator shells of level below $N$, the first four shell closures are
--
--   $$S_1 = 2, \qquad S_2 = 8, \qquad S_3 = 20, \qquad S_4 = 40.$$
--
--   Equivalently, $2 = 2$, $8 = 2+6$, $20 = 2+6+12$ and $40 = 2+6+12+20$. These four numbers are the prediction the harmonic-oscillator model makes for the magic numbers, and the values against which the model is judged in the next milestone.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem cumulativeCapacity_first_values :
    List.map cumulativeCapacity [1, 2, 3, 4] = [2, 8, 20, 40] := by sorry

end MagicNumberShellModel
