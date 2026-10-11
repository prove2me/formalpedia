-- Prove2me | Theorems.Thm_NoetherianScheme_isNoetherianScheme_iff_compactSpace_and_affineOpens
-- name    : NoetherianScheme.isNoetherianScheme_iff_compactSpace_and_affineOpens
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-10T22:31:57.658122+00:00
-- url     : https://prove2.me/theorems/6aab351c-ab02-4396-a353-002786e57d06
-- title:
--   Noetherian schemes: quasi-compact with Noetherian affine sections
-- statement:
--   Let $X$ be a scheme. Then $X$ is a Noetherian scheme (it admits a finite cover by open affines with Noetherian rings of sections) if and only if
--
--   1. the underlying topological space of $X$ is (quasi-)compact, and
--   2. for **every** open affine subset $U \subseteq X$, the ring $\Gamma(X,U)$ is Noetherian.
--
--   $$X \text{ Noetherian} \iff X \text{ quasi-compact and } \Gamma(X,U) \text{ Noetherian for all affine open } U \subseteq X.$$
--
--   This is the characterization stated in the opening section of the source: being Noetherian is independent of the chosen affine cover, so the finite-cover definition can be replaced by a condition on all affine opens together with compactness.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section: definition, "a scheme is Noetherian if and only if it is locally Noetherian and compact", and "in a locally Noetherian scheme, if Spec A ⊆ X is an open affine subset, then A is a Noetherian ring".

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem isNoetherianScheme_iff_compactSpace_and_affineOpens (X : Scheme.{u}) :
    IsNoetherianScheme X ↔
      CompactSpace X ∧ ∀ U ∈ X.affineOpens, IsNoetherianRing Γ(X, U) := by sorry

end NoetherianScheme
