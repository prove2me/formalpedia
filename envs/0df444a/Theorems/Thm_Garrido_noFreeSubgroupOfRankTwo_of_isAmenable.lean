-- Prove2me | Theorems.Thm_Garrido_noFreeSubgroupOfRankTwo_of_isAmenable
-- name    : Garrido.noFreeSubgroupOfRankTwo_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:04:38.153386+00:00
-- url     : https://prove2.me/theorems/185138b1-296a-4ea7-8a61-299815357e7b
-- title:
--   AG ⊆ NF (p. 11) — an amenable group has no free subgroup of rank two
-- statement:
--   An amenable group contains no free subgroup of rank two:
--
--   $$G \text{ amenable} \implies G \text{ has no subgroup isomorphic to } F_2,$$
--
--   that is, $AG \subseteq NF$. It is the inclusion whose converse is von Neumann's problem, answered
--   negatively by Ol'shanskii.
--
--   **Formalization Note.** Amenability is the imported `IsAmenable`, and "no free subgroup of rank
--   two" is the imported `Chou.NoFreeSubgroupOfRankTwo`: no homomorphism from `FreeGroup (Fin 2)`
--   to $G$ is injective.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 4, 11, the remark after Definition 1.12 and the displayed inclusion EG ⊆ AG ⊆ NF; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The inclusion goes back to J. von Neumann, "Zur allgemeinen Theorie des Masses", Fund. Math. 13 (1929), 73–116; https://doi.org/10.4064/fm-13-1-73-116

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

namespace Garrido

theorem noFreeSubgroupOfRankTwo_of_isAmenable {G : Type*} [Group G] (hG : IsAmenable G) :
    Chou.NoFreeSubgroupOfRankTwo G := by
  sorry

end Garrido
