-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_stdLat
-- name    : GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:13.639509+00:00
-- url     : https://prove2.me/theorems/9ffebc13-3e3a-44dc-8305-e828a0c6fa98
-- title:
--   Fourier Depth: mem mat Lat smul std Lat
-- statement:
--   The Fourier Depth construction uses the mem mat Lat smul std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L33-L36

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
omit [DecidableEq D]

theorem GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat {c : kˣ} {X : Matrix A D k} :
    X ∈ matLat A (c • stdLat k D) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by sorry
