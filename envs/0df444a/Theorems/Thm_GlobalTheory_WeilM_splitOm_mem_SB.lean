-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_splitOm_mem_SB
-- name    : GlobalTheory.WeilM.splitOm_mem_SB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:26.2908+00:00
-- url     : https://prove2.me/theorems/e5a25b08-89f8-4c3d-87f7-f21a0fb5d9e0
-- title:
--   Weil M: split Om mem SB
-- statement:
--   The Weil M construction uses the split Om mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L246-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L246-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
omit [DecidableEq α] [Fintype κ]

theorem GlobalTheory.WeilM.splitOm_mem_SB [TopologicalSpace R] [IsTopologicalRing R] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle)
    (J : Matrix β β (R × R)) (σ : κ ≃ α × β) (h : UG (swapA R) J) {φ : (κ → R) → ℂ} (hφ : φ ∈ SB (κ → R)) :
    splitOm m χ J σ h φ ∈ SB (κ → R) := by sorry
