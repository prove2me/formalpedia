-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianScheme_iff_isLocallyNoetherianScheme_and_compactSpace
-- name    : NoetherianScheme.isNoetherianScheme_iff_isLocallyNoetherianScheme_and_compactSpace
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:32:36.709995+00:00
-- url     : https://prove2.me/theorems/5b0746a3-7631-46d3-9b4c-8292567f70e7
-- title:
--   Noetherian ⇔ locally Noetherian and quasi-compact
-- statement:
--   Let $X$ be a scheme. Then
--   $$X \text{ is Noetherian} \iff X \text{ is locally Noetherian and } X \text{ is (quasi-)compact}.$$
--   Here "Noetherian" means covered by finitely many open affines with Noetherian rings of sections, and "locally Noetherian" means covered by (possibly infinitely many) such open affines.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 1: "Thus, a scheme is Noetherian if and only if it is locally Noetherian and compact."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianScheme_iff_isLocallyNoetherianScheme_and_compactSpace (X : Scheme.{u}) :
    IsNoetherianScheme X ↔ IsLocallyNoetherianScheme X ∧ CompactSpace X := by sorry

end NoetherianScheme
