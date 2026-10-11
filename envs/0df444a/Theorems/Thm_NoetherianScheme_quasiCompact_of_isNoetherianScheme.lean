-- Prove2me | Theorems.Thm_NoetherianScheme_quasiCompact_of_isNoetherianScheme
-- name    : NoetherianScheme.quasiCompact_of_isNoetherianScheme
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:37:38.1123+00:00
-- url     : https://prove2.me/theorems/355bb1e1-9e12-4e83-ae67-675ba2c4fe40
-- title:
--   Morphisms from a Noetherian scheme are quasi-compact
-- statement:
--   Let $f : X \to S$ be any morphism of schemes with $X$ Noetherian. Then $f$ is **quasi-compact**: for every quasi-compact open $V \subseteq S$, the preimage $f^{-1}(V)$ is quasi-compact.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Properties and Noetherian hypotheses": "Every morphism from a Noetherian scheme X → S is quasi-compact." [2] = Stacks Project Lemma 28.5.8 (Tag 01P0).

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem quasiCompact_of_isNoetherianScheme {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : IsNoetherianScheme X) : QuasiCompact f := by sorry

end NoetherianScheme
