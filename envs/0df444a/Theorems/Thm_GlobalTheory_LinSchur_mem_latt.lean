-- Prove2me | Theorems.Thm_GlobalTheory_LinSchur_mem_latt
-- name    : GlobalTheory.LinSchur.mem_latt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:31.57051+00:00
-- url     : https://prove2.me/theorems/03344982-676a-4b2a-8805-dd4ce49f41cf
-- title:
--   Lin Schur: mem latt
-- statement:
--   The Lin Schur construction uses the mem latt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AddCharNegEqOne.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AddCharNegEqOne.lean#L32-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LinSchur
variable {k : Type} [Field k] [ValuativeRel k]

theorem GlobalTheory.LinSchur.mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := by sorry
