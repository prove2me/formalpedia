-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_ker_eq_nilradical
-- name    : GlobalTheory.OnePoint.ker_eq_nilradical
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:44.964807+00:00
-- url     : https://prove2.me/theorems/d1a52c6d-bb13-4368-a117-2326fea6ec18
-- title:
--   One Point: ker eq nilradical
-- statement:
--   The One Point construction uses the ker eq nilradical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L132-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))

theorem GlobalTheory.OnePoint.ker_eq_nilradical {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) [QuasiCompact g]
    [Surjective g] : g.ker = X.nilradical := by sorry
