-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_mk_eq_mk_iff
-- name    : GroundTheory.Brauer.H2mul.mk_eq_mk_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:21.727961+00:00
-- url     : https://prove2.me/theorems/2a4960a8-dcb2-4565-b9ec-60a1dff208a0
-- title:
--   H2mul: mk eq mk iff
-- statement:
--   The H2mul construction uses the mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L109-L112

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

theorem GroundTheory.Brauer.H2mul.mk_eq_mk_iff (f f' : mulCocycles₂ G M) :
    mk G M f = mk G M f' ↔ IsMulCoboundary₂ ((f : G × G → M) / (f' : G × G → M)) := by sorry
