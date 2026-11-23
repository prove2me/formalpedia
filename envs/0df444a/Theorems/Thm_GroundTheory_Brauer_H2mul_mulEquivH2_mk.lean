-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
-- name    : GroundTheory.Brauer.H2mul.mulEquivH2_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:00.630525+00:00
-- url     : https://prove2.me/theorems/e831d281-3d35-4edb-b0df-e3ef89c242b7
-- title:
--   H2mul: mul Equiv H2 mk
-- statement:
--   The H2mul construction uses the mul Equiv H2 mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L331-L334

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
variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul

theorem GroundTheory.Brauer.H2mul.mulEquivH2_mk (c : mulCocycles₂ G M) :
    mulEquivH2 (mk G M c) = Multiplicative.ofAdd (H2π (Rep.ofMulDistribMulAction G M)
      (cocyclesOfIsMulCocycle₂ (f := (c : G × G → M)) c.2)) := by sorry

attribute [defeq] GroundTheory.Brauer.H2mul.mulEquivH2_mk
