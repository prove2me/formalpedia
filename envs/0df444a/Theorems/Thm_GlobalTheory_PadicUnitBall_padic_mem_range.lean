-- Prove2me | Theorems.Thm_GlobalTheory_PadicUnitBall_padic_mem_range
-- name    : GlobalTheory.PadicUnitBall.padic_mem_range
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:51.799496+00:00
-- url     : https://prove2.me/theorems/7602e007-60a9-4c06-b8cf-1ecd03eb3d6b
-- title:
--   Padic Unit Ball: padic mem range
-- statement:
--   The Padic Unit Ball construction uses the padic mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L129-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L129-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall

theorem GlobalTheory.PadicUnitBall.padic_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by sorry
