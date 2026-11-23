-- Prove2me | Theorems.Thm_GlobalTheory_CharDualMat_valuation_nsmul_le
-- name    : GlobalTheory.CharDualMat.valuation_nsmul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:52.102582+00:00
-- url     : https://prove2.me/theorems/6b94fe82-903c-47ef-bc31-0916c7792fae
-- title:
--   Char Dual Mat: valuation nsmul le
-- statement:
--   The Char Dual Mat construction uses the valuation nsmul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegralOfAddCharTraceDual.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegralOfAddCharTraceDual.lean#L77-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CharDualMat.valuation_nsmul_le (t : k) (n : ℕ) : valuation k (n • t) ≤ valuation k t := by sorry
