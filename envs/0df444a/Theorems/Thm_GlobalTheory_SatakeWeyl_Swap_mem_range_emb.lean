-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Swap_mem_range_emb
-- name    : GlobalTheory.SatakeWeyl.Swap.mem_range_emb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:38.884936+00:00
-- url     : https://prove2.me/theorems/28c1a72e-1c62-4586-bd61-1b9a9dc997a7
-- title:
--   Swap: mem range emb
-- statement:
--   The Swap construction uses the mem range emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffAdjacentSwapOfLeviReduction.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffAdjacentSwapOfLeviReduction.lean#L61-L67

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap

theorem GlobalTheory.SatakeWeyl.Swap.mem_range_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) (a : Fin n) :
    a ∈ Set.range (emb n i h) ↔ a.val = i ∨ a.val = i + 1 ∨ a.val = n - 2 - i ∨ a.val = n - 1 - i := by sorry
