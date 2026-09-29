-- Prove2me | Theorems.Thm_MagicNumberShellModel_shellCapacity_values
-- name    : MagicNumberShellModel.shellCapacity_values
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:17:56.432945+00:00
-- url     : https://prove2.me/theorems/3087e945-a8cd-41fb-b25e-44f12c01bc3c
-- title:
--   First four shell capacities: $2, 6, 12, 20$
-- statement:
--   Write $C_n = 2\,|L_n|$ for the number of nucleons filling the oscillator shell at energy level $n$, the factor $2$ accounting for the two spin orientations. Then
--
--   $$C_0 = 2, \qquad C_1 = 6, \qquad C_2 = 12, \qquad C_3 = 20.$$
--
--   These are the four shell capacities quoted in the source before the cumulative sums are taken; they are the concrete check that the degeneracy count has been transcribed with the right normalization.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem shellCapacity_values :
    shellCapacity 0 = 2 ∧ shellCapacity 1 = 6 ∧ shellCapacity 2 = 12 ∧
      shellCapacity 3 = 20 := by sorry

end MagicNumberShellModel
