-- Prove2me | Theorems.Thm_GlobalTheory_PosOneCell_app_smul
-- name    : GlobalTheory.PosOneCell.app_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:22.663416+00:00
-- url     : https://prove2.me/theorems/47ef445c-a566-42d7-87a3-28bddc9f2213
-- title:
--   Pos One Cell: app smul
-- statement:
--   The Pos One Cell construction uses the app smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/QuotIntPosOne.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/QuotIntPosOne.lean#L20-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsQuotIntCellsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_QuotIntPosOne
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)
noncomputable section
open GlobalTheory GlobalTheory.PosOneCell
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.PosOneCell.app_smul (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by sorry
