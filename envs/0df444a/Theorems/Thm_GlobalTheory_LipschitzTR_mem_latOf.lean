-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf
-- name    : GlobalTheory.LipschitzTR.mem_latOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:00.817903+00:00
-- url     : https://prove2.me/theorems/f7e95bbf-a1e4-4869-b790-4d47f95688e3
-- title:
--   Lipschitz TR: mem lat Of
-- statement:
--   The Lipschitz TR construction uses the mem lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RembApply.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RembApply.lean#L26-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.LipschitzTR
variable (F : Type) [Field F] [NumberField F]
variable {F}

theorem GlobalTheory.LipschitzTR.mem_latOf (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by sorry
