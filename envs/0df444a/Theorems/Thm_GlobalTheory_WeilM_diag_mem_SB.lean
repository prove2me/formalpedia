-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_diag_mem_SB
-- name    : GlobalTheory.WeilM.diag_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:56.284479+00:00
-- url     : https://prove2.me/theorems/796e8345-e954-4ef9-a5a8-9a7b3fda008a
-- title:
--   Weil M: diag mem SB
-- statement:
--   The Weil M construction uses the diag mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L28-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem GlobalTheory.WeilM.diag_mem_SB [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by sorry
