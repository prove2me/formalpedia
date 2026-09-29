-- Prove2me | Theorems.Thm_Garrido_isAmenable_of_isAmenable_of_isAmenable_quotient
-- name    : Garrido.isAmenable_of_isAmenable_of_isAmenable_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:31:48.82514+00:00
-- url     : https://prove2.me/theorems/75a5dbe3-f69c-47ce-9935-6a1d150463a6
-- title:
--   Proposition 2.2(2) — amenability is closed under extensions
-- statement:
--   Let $N \le G$ be a normal subgroup. If $N$ is amenable and $G/N$ is amenable,
--   then $G$ is amenable.
--
--   Both hypotheses are amenability in the sense of the mission's definition: $N$ as a group in its
--   own right, and $G/N$ as the quotient group.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 6, Proposition 2.2(2); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_of_isAmenable_of_isAmenable_quotient {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsAmenable N) (hQ : IsAmenable (G ⧸ N)) :
    IsAmenable G := by
  sorry

end Garrido
