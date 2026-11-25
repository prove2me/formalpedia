-- Prove2me | Theorems.Thm_GlobalTheory_T_padic_mem_range_complete_dvr_padicAlgCl
-- name    : GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:46.768721+00:00
-- url     : https://prove2.me/theorems/2bda2a56-af4a-47a3-b7f3-a0edf1439d5b
-- title:
--   T: padic mem range complete dvr padic Alg Cl
-- statement:
--   The T construction uses the padic mem range complete dvr padic Alg Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgClStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgClStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgClStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by sorry
