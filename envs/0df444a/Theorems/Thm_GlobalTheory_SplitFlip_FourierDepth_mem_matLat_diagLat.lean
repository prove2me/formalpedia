-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_diagLat
-- name    : GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:27.130064+00:00
-- url     : https://prove2.me/theorems/9b461fcd-2980-4f22-98f2-ea8a2adf5e78
-- title:
--   Fourier Depth: mem mat Lat diag Lat
-- statement:
--   The Fourier Depth construction uses the mem mat Lat diag Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L28-L29

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

theorem GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat {c : D → kˣ} {X : Matrix A D k} :
    X ∈ matLat A (diagLat c) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c j : k) := by sorry
