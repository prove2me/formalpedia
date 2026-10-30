-- Prove2me | Theorems.Thm_JuschenkoMonod_isAmenable_of_isAmenableAction_of_isAmenable_stabilizer
-- name    : JuschenkoMonod.isAmenable_of_isAmenableAction_of_isAmenable_stabilizer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:27:00.236331+00:00
-- url     : https://prove2.me/theorems/e9a80627-412f-4a78-b0e7-23e178a75d15
-- title:
--   Lemma 3.2 — a group acting with an invariant mean and with amenable stabilisers is amenable
-- statement:
--   Let a group $H$ act on a set $Y$, and suppose the action admits an $H$-invariant mean (a finitely additive probability measure on all subsets of $Y$). If the stabiliser in $H$ of every $y \in Y$ is amenable, then $H$ is amenable.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 784, Lemma 3.2

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange

namespace JuschenkoMonod

theorem isAmenable_of_isAmenableAction_of_isAmenable_stabilizer (H Y : Type*) [Group H]
    [MulAction H Y] (hY : IntervalExchange.IsAmenableAction H Y)
    (hstab : ∀ y : Y, Garrido.IsAmenable (MulAction.stabilizer H y)) : Garrido.IsAmenable H := by
  sorry

end JuschenkoMonod
