-- Prove2me | Theorems.Thm_NoetherianScheme_exists_valuationRing_noetherianSpace_not_isNoetherianScheme
-- name    : NoetherianScheme.exists_valuationRing_noetherianSpace_not_isNoetherianScheme
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:36:46.224619+00:00
-- url     : https://prove2.me/theorems/2489f22d-a378-4dc9-947a-6d9e9a52b743
-- title:
--   Converse fails: Spec of a non-Noetherian valuation ring
-- statement:
--   There exists a valuation ring $R$ (an integral domain in which, for any two elements, one divides the other) such that
--
--   1. $R$ is not a Noetherian ring,
--   2. the underlying space of $\operatorname{Spec} R$ is a Noetherian topological space, and
--   3. $\operatorname{Spec} R$ is not a Noetherian scheme.
--
--   So the converse of "a Noetherian scheme is a Noetherian topological space" is false.
--
--   **Formalization Note** Not every non-Noetherian valuation ring works (a valuation ring of infinite rank has a non-Noetherian spectrum), so the source's "consider the spectrum of a non-Noetherian valuation ring" is encoded as an existence statement. The ring is taken in the lowest universe.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 3: "But the converse is false in general; consider, for example, the spectrum of a non-Noetherian valuation ring."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem exists_valuationRing_noetherianSpace_not_isNoetherianScheme :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R), ValuationRing R ∧ ¬ IsNoetherianRing R ∧
      TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of R)) ∧
      ¬ IsNoetherianScheme (Spec (CommRingCat.of R)) := by sorry

end NoetherianScheme
