-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianRing_of_mem_affineOpens
-- name    : NoetherianScheme.isNoetherianRing_of_mem_affineOpens
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:33:05.162311+00:00
-- url     : https://prove2.me/theorems/f0d7cf0d-cca9-4111-b456-41b2d7e49a8f
-- title:
--   Affine opens of a locally Noetherian scheme have Noetherian sections
-- statement:
--   Let $X$ be a locally Noetherian scheme and let $U \subseteq X$ be **any** open affine subset (so $U \cong \operatorname{Spec} A$ with $A = \Gamma(X,U)$). Then
--   $$A = \Gamma(X,U) \text{ is a Noetherian ring.}$$
--   The point is that $U$ need not be one of the affines in a cover witnessing local Noetherianity.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 2: "in a locally Noetherian scheme, if Spec A ⊆ X is an open affine subset, then A is a Noetherian ring".

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianRing_of_mem_affineOpens (X : Scheme.{u}) (hX : IsLocallyNoetherianScheme X)
    (U : X.Opens) (hU : U ∈ X.affineOpens) : IsNoetherianRing Γ(X, U) := by sorry

end NoetherianScheme
