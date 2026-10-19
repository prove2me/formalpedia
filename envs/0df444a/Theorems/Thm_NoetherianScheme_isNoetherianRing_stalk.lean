-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianRing_stalk
-- name    : NoetherianScheme.isNoetherianRing_stalk
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:35:28.99696+00:00
-- url     : https://prove2.me/theorems/f4df8e45-e60f-4aee-af0e-2adcdcae447b
-- title:
--   Local rings of a locally Noetherian scheme are Noetherian
-- statement:
--   Let $X$ be a locally Noetherian scheme and $x \in X$ a point. Then the local ring
--   $$\mathcal O_{X,x} = \varinjlim_{x \in V} \mathcal O_X(V)$$
--   (the stalk of the structure sheaf at $x$) is a Noetherian ring.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 2: "For a locally Noetherian scheme X, the local rings O_{X,x} are also Noetherian rings."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianRing_stalk (X : Scheme.{u}) (hX : IsLocallyNoetherianScheme X) (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by sorry

end NoetherianScheme
