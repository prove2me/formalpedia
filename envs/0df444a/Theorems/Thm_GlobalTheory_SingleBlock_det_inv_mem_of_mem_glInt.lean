-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_det_inv_mem_of_mem_glInt
-- name    : GlobalTheory.SingleBlock.det_inv_mem_of_mem_glInt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:01.967845+00:00
-- url     : https://prove2.me/theorems/8fb23d72-3e6d-4f06-8602-d8dc0d34f235
-- title:
--   Single Block: det inv mem of mem gl Int
-- statement:
--   The Single Block construction uses the det inv mem of mem gl Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L36-L38

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F]

theorem GlobalTheory.SingleBlock.det_inv_mem_of_mem_glInt {O : Subring F} {n : Type} [Fintype n] [DecidableEq n]
    {g : GL n F} (hg : g ∈ glInt O n) : (((GeneralLinearGroup.det g)⁻¹ : Fˣ) : F) ∈ O := by sorry
