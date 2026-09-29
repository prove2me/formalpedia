-- Prove2me | Theorems.Thm_Garrido_exists_countable_isParadoxical_compl
-- name    : Garrido.exists_countable_isParadoxical_compl
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:01:04.31438+00:00
-- url     : https://prove2.me/theorems/f873812d-cfcd-4ad7-b944-7512cdc1b89a
-- title:
--   Theorem 1.7 — the Hausdorff paradox
-- statement:
--   There is a countable set $D \subseteq S^2$ such that the rest of the sphere,
--   $S^2 \setminus D$, is $SO(3,\mathbb{R})$-paradoxical:
--
--   $$\exists\, D \subseteq S^2 \text{ countable} : \quad S^2 \setminus D \text{ is } SO(3,\mathbb{R})\text{-paradoxical}.$$
--
--   It is the sphere-level form of the paradox, before the countable exceptional set is absorbed.
--
--   **Formalization Note.** Paradoxicality is the imported `IsParadoxical`, relative to the subset
--   $S^2 \setminus D$ (the complement of $D$ in `Sphere 2`), for the rotation action on the sphere:
--   the pieces lie in $S^2 \setminus D$ and are moved by rotations. "Countable" allows finite.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, Theorem 1.7 (Hausdorff Paradox); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The result is due to F. Hausdorff, "Bemerkung über den Inhalt von Punktmengen", Math. Ann. 75 (1914), 428–433; https://doi.org/10.1007/BF01563735

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem exists_countable_isParadoxical_compl :
    ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ := by
  sorry

end Garrido
