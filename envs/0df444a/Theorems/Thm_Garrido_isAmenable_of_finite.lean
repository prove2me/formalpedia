-- Prove2me | Theorems.Thm_Garrido_isAmenable_of_finite
-- name    : Garrido.isAmenable_of_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:12:03.184443+00:00
-- url     : https://prove2.me/theorems/fcb8a30d-fefd-43d8-b649-4357956f2b95
-- title:
--   Example 2.1 — every finite group is amenable
-- statement:
--   Every finite group is amenable: for a group $G$ with finitely many elements
--   there is a finitely additive left-invariant $m : \mathcal{P}(G) \to [0,\infty]$ with
--   $m(G) = 1$.
--
--   Finiteness is a typeclass hypothesis. The source's witness is the normalised counting measure
--   $m(A) = |A|/|G|$, which is well defined because a finite group is nonempty.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 5, Example 2.1; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] : IsAmenable G := by
  sorry

end Garrido
