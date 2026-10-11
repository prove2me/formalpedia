-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianScheme_of_finiteType
-- name    : NoetherianScheme.isNoetherianScheme_of_finiteType
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:41:13.437841+00:00
-- url     : https://prove2.me/theorems/85f6cd59-6d71-4ca2-88c0-57fd447ae022
-- title:
--   Finite type over a Noetherian base is Noetherian
-- statement:
--   Let $f : X \to S$ be a morphism of schemes of **finite type** (locally of finite type and quasi-compact). If $S$ is Noetherian, then $X$ is Noetherian.
--
--   This covers the families $X \to S$ discussed in the source: schemes of finite type over a Noetherian base are Noetherian.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Examples / Locally of finite type over a Noetherian base": "families of schemes X → S where the base S is Noetherian and X is of finite type over S"; Stacks Project Lemma 28.5.7 / 29.15.6.

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianScheme_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (hS : IsNoetherianScheme S) :
    IsNoetherianScheme X := by sorry

end NoetherianScheme
