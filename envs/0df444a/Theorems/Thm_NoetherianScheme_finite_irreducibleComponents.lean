-- Prove2me | Theorems.Thm_NoetherianScheme_finite_irreducibleComponents
-- name    : NoetherianScheme.finite_irreducibleComponents
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:37:12.881565+00:00
-- url     : https://prove2.me/theorems/b0020bc7-ed20-43ed-a6a3-166fb2161b47
-- title:
--   A Noetherian scheme has finitely many irreducible components
-- statement:
--   Let $X$ be a Noetherian scheme. Then the set of irreducible components of $X$ (the maximal irreducible closed subsets of its underlying space) is finite.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Properties and Noetherian hypotheses": "Any Noetherian scheme can only have finitely many irreducible components." [1] = Stacks Project Lemma 28.5.7 (Tag 0BA8).

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem finite_irreducibleComponents (X : Scheme.{u}) (hX : IsNoetherianScheme X) :
    (irreducibleComponents X).Finite := by sorry

end NoetherianScheme
