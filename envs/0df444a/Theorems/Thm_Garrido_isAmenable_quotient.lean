-- Prove2me | Theorems.Thm_Garrido_isAmenable_quotient
-- name    : Garrido.isAmenable_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:12:53.737358+00:00
-- url     : https://prove2.me/theorems/c934df91-59cc-4412-8059-ec46de4994cb
-- title:
--   Proposition 2.2(1b) — a quotient of an amenable group is amenable
-- statement:
--   If $G$ is amenable and $N \le G$ is a normal subgroup, then the quotient group
--   $G/N$ is amenable.
--
--   Normality is a typeclass hypothesis on $N$, as it must be for the quotient to be a group. The
--   source's proof pushes the measure forward along the quotient map.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 6, Proposition 2.2(1), second assertion; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_quotient {G : Type*} [Group G] (hG : IsAmenable G)
    (N : Subgroup G) [N.Normal] : IsAmenable (G ⧸ N) := by
  sorry

end Garrido
