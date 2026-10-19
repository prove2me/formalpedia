-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianScheme_Spec_iff
-- name    : NoetherianScheme.isNoetherianScheme_Spec_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:34:34.285293+00:00
-- url     : https://prove2.me/theorems/bd94a6d4-aba9-469b-806e-83530527b944
-- title:
--   Spec A is Noetherian iff A is Noetherian
-- statement:
--   Let $A$ be a commutative ring. Then
--   $$\operatorname{Spec} A \text{ is a Noetherian scheme} \iff A \text{ is a Noetherian ring}.$$
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 2: "in particular, Spec A is a Noetherian scheme if and only if A is a Noetherian ring".

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianScheme_Spec_iff (A : Type u) [CommRing A] :
    IsNoetherianScheme (Spec (CommRingCat.of A)) ↔ IsNoetherianRing A := by sorry

end NoetherianScheme
