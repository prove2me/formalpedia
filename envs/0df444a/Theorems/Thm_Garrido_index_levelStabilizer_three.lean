-- Prove2me | Theorems.Thm_Garrido_index_levelStabilizer_three
-- name    : Garrido.index_levelStabilizer_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:12:03.07726+00:00
-- url     : https://prove2.me/theorems/1736a31e-e111-45d5-b259-16a835f3147f
-- title:
--   p. 16 — St(3) has index 2⁷ in Γ
-- statement:
--   The third level stabilizer has index $2^7 = 128$ in $\Gamma$:
--
--   $$|\Gamma : St(3)| = 2^7.$$
--
--   **Formalization Note.** The index is Mathlib's `Subgroup.index`.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 16, the proof of Theorem 4.9; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem index_levelStabilizer_three : (levelStabilizer 3).index = 2 ^ 7 := by
  sorry

end Garrido
