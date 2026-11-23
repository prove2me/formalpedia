-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_nilradical_le_ker
-- name    : GlobalTheory.OnePoint.nilradical_le_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:45.669683+00:00
-- url     : https://prove2.me/theorems/2076340d-7a93-4ab1-a9d5-b5c103b73313
-- title:
--   One Point: nilradical le ker
-- statement:
--   The One Point construction uses the nilradical le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L126-L130

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

theorem GlobalTheory.OnePoint.nilradical_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) :
    X.nilradical ≤ g.ker := by sorry
