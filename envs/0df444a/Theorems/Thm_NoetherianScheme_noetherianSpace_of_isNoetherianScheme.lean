-- Prove2me | Theorems.Thm_NoetherianScheme_noetherianSpace_of_isNoetherianScheme
-- name    : NoetherianScheme.noetherianSpace_of_isNoetherianScheme
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:35:56.570344+00:00
-- url     : https://prove2.me/theorems/55581802-5a66-456c-a80a-7bf943897705
-- title:
--   A Noetherian scheme is a Noetherian topological space
-- statement:
--   Let $X$ be a Noetherian scheme. Then its underlying topological space is a **Noetherian topological space**: every descending chain of closed subsets
--   $$Z_1 \supseteq Z_2 \supseteq Z_3 \supseteq \cdots$$
--   is eventually constant (equivalently, every open subset is compact).
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 3: "A Noetherian scheme is a Noetherian topological space."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem noetherianSpace_of_isNoetherianScheme (X : Scheme.{u}) (hX : IsNoetherianScheme X) :
    TopologicalSpace.NoetherianSpace X := by sorry

end NoetherianScheme
