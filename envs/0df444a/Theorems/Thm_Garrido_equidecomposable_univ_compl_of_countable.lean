-- Prove2me | Theorems.Thm_Garrido_equidecomposable_univ_compl_of_countable
-- name    : Garrido.equidecomposable_univ_compl_of_countable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:02:05.767394+00:00
-- url     : https://prove2.me/theorems/14c80e85-64e9-427c-9230-91dd4c512920
-- title:
--   Proposition 1.8 — S² and S² minus a countable set are SO(3,ℝ)-equidecomposable
-- statement:
--   For every countable set $D \subseteq S^2$, the whole sphere and the sphere with $D$
--   removed are $SO(3,\mathbb{R})$-equidecomposable:
--
--   $$S^2 \sim S^2 \setminus D.$$
--
--   With the Hausdorff paradox and transitivity of $\sim$, it upgrades "the sphere minus a
--   countable set is paradoxical" to "the sphere is paradoxical".
--
--   **Formalization Note.** Equidecomposability is the imported `Equidecomposable`, for the rotation
--   action on `Sphere 2`.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, Proposition 1.8; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem equidecomposable_univ_compl_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ := by
  sorry

end Garrido
