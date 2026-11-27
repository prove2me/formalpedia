-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_mapPair_id
-- name    : GroundTheory.Brauer.H2mul.mapPair_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:36.637478+00:00
-- url     : https://prove2.me/theorems/5ad12ed1-6070-40cb-9fdf-690ddceab761
-- title:
--   H2mul: map Pair id
-- statement:
--   The H2mul construction uses the map Pair id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L174-L177

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
variable {G M}
variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

theorem GroundTheory.Brauer.H2mul.mapPair_id : mapPair (MonoidHom.id G) (MonoidHom.id M) (fun _ _ => rfl) =
    MonoidHom.id (H2mul G M) := by sorry
