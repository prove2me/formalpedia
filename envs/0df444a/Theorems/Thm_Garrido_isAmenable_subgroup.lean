-- Prove2me | Theorems.Thm_Garrido_isAmenable_subgroup
-- name    : Garrido.isAmenable_subgroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:12:23.254465+00:00
-- url     : https://prove2.me/theorems/719e5ab8-56b6-4780-82ed-715bbd16b8a2
-- title:
--   Proposition 2.2(1a) — a subgroup of an amenable group is amenable
-- statement:
--   If $G$ is amenable then every subgroup $H \le G$ is amenable, where $H$ is
--   regarded as a group in its own right.
--
--   No normality and no finite-index hypothesis: $H$ is an arbitrary subgroup. The source's proof
--   picks a right transversal $M$ of $H$ in $G$ using the axiom of choice and sets
--   $\nu(A) = \mu(AM)$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 6, Proposition 2.2(1), first assertion; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_subgroup {G : Type*} [Group G] (hG : IsAmenable G) (H : Subgroup G) :
    IsAmenable H := by
  sorry

end Garrido
