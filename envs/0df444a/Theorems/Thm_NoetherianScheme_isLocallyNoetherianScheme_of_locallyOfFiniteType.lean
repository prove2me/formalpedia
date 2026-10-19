-- Prove2me | Theorems.Thm_NoetherianScheme_isLocallyNoetherianScheme_of_locallyOfFiniteType
-- name    : NoetherianScheme.isLocallyNoetherianScheme_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:40:42.227151+00:00
-- url     : https://prove2.me/theorems/0ad24ae6-bdcd-40fa-9d8f-279843afbbc4
-- title:
--   Locally finite type over locally Noetherian is locally Noetherian
-- statement:
--   Let $f : X \to S$ be a morphism of schemes that is **locally of finite type** (for affine opens $V = \operatorname{Spec} B \subseteq S$ and $U = \operatorname{Spec} A \subseteq f^{-1}(V)$, $A$ is a finitely generated $B$-algebra). If $S$ is locally Noetherian, then $X$ is locally Noetherian.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Examples / Locally of finite type over a Noetherian base", reference [5] = Stacks Project Lemma 29.15.6 (Tag 01T6): "Let f : X → S be a morphism. If S is locally Noetherian and f locally of finite type then X is locally Noetherian."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isLocallyNoetherianScheme_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (hS : IsLocallyNoetherianScheme S) :
    IsLocallyNoetherianScheme X := by sorry

end NoetherianScheme
