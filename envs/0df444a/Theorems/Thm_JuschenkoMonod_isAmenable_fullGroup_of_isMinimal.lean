-- Prove2me | Theorems.Thm_JuschenkoMonod_isAmenable_fullGroup_of_isMinimal
-- name    : JuschenkoMonod.isAmenable_fullGroup_of_isMinimal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:32:46.668105+00:00
-- url     : https://prove2.me/theorems/2e28a92d-dd2e-4120-9069-8ad58dff44f8
-- title:
--   Theorem A — the topological full group of any minimal Cantor system is amenable
-- statement:
--   Let $T$ be a minimal homeomorphism of a Cantor space $C$ (no closed set $S$ with $T(S) = S$ other than $\emptyset$ and $C$). Then the topological full group $[[T]]$, the group of homeomorphisms $h$ of $C$ such that every point has a neighbourhood on which $h$ agrees with some power of $T$, is amenable: it carries a left-invariant finitely additive probability measure defined on all its subsets.
--
--   Juschenko–Monod, p. 776: “**Theorem A.** *The topological full group of any minimal Cantor system is amenable.*”
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 776, Theorem A

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem isAmenable_fullGroup_of_isMinimal (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C) (hT : IsMinimal T) :
    Garrido.IsAmenable (fullGroup T) := by
  sorry

end JuschenkoMonod
