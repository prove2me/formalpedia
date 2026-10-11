-- Prove2me | Theorems.Thm_NoetherianScheme_not_isNoetherianRing_adeleRing
-- name    : NoetherianScheme.not_isNoetherianRing_adeleRing
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:41:53.810826+00:00
-- url     : https://prove2.me/theorems/055110ea-de00-431a-8495-7cf67ab6b905
-- title:
--   The adele ring of a number field is not Noetherian
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and let
--   $$\mathbb A_K = K_\infty \times \prod\nolimits'_{v<\infty} K_v$$
--   be its ring of adeles (the infinite adeles times the restricted product of the completions at the finite places). Then $\mathbb A_K$ is **not** a Noetherian ring.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Non-examples / Schemes over Adelic bases": "One of the natural rings which are non-Noetherian are the ring of adeles A_K for an algebraic number field K."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem not_isNoetherianRing_adeleRing (K : Type u) [Field K] [NumberField K] :
    ¬ IsNoetherianRing (AdeleRing (𝓞 K) K) := by sorry

end NoetherianScheme
