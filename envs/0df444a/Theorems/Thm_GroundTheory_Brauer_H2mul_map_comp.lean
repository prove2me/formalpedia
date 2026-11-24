-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_map_comp
-- name    : GroundTheory.Brauer.H2mul.map_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:21.206726+00:00
-- url     : https://prove2.me/theorems/caf2d804-ab59-4661-841b-739b1d251844
-- title:
--   H2mul: map comp
-- statement:
--   The H2mul construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L203-L206

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
variable {N : Type v'} [CommGroup N] [MulDistribMulAction G N]

theorem GroundTheory.Brauer.H2mul.map_comp {P : Type*} [CommGroup P] [MulDistribMulAction G P] (φ : M →*[G] N)
    (ψ : N →*[G] P) : map (ψ.comp φ) = (map ψ).comp (map φ) := by sorry
