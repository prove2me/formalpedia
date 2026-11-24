-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_pairCols_add
-- name    : GlobalTheory.SplitFlip.FourierDepth.pairCols_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:12.778465+00:00
-- url     : https://prove2.me/theorems/91003ee9-47bc-424b-a696-fe77dd282a5e
-- title:
--   Fourier Depth: pair Cols add
-- statement:
--   The Fourier Depth construction uses the pair Cols add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.FourierDepth
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D]

theorem GlobalTheory.SplitFlip.FourierDepth.pairCols_add [Fintype A] (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    pairCols P (Y + Z) T = pairCols P Y T + pairCols P Z T := by sorry
