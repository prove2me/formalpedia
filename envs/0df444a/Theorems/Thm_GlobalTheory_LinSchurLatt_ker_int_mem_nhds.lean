-- Prove2me | Theorems.Thm_GlobalTheory_LinSchurLatt_ker_int_mem_nhds
-- name    : GlobalTheory.LinSchurLatt.ker_int_mem_nhds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:57.312341+00:00
-- url     : https://prove2.me/theorems/706729b0-fa2f-47e6-85a1-30ea5e63d158
-- title:
--   Lin Schur Latt: ker int mem nhds
-- statement:
--   The Lin Schur Latt construction uses the ker int mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L40-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.LinSchurLatt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LinSchurLatt.ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by sorry
