-- Prove2me | Theorems.Thm_Garrido_isAmenable_of_commGroup
-- name    : Garrido.isAmenable_of_commGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:33:48.953983+00:00
-- url     : https://prove2.me/theorems/fab2498c-ba87-4ac8-acee-ac1e7b458ec1
-- title:
--   Proposition 2.3 — every abelian group is amenable
-- statement:
--   Every abelian group is amenable. Commutativity is a typeclass hypothesis; there
--   is no finiteness or finite-generation assumption, so the statement covers arbitrary abelian
--   groups.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 6, Proposition 2.3; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_of_commGroup (G : Type*) [CommGroup G] : IsAmenable G := by
  sorry

end Garrido
