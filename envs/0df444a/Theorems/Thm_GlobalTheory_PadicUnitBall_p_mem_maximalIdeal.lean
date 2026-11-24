-- Prove2me | Theorems.Thm_GlobalTheory_PadicUnitBall_p_mem_maximalIdeal
-- name    : GlobalTheory.PadicUnitBall.p_mem_maximalIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:26.592045+00:00
-- url     : https://prove2.me/theorems/3a91c905-133c-45c4-8298-f921a6e7824f
-- title:
--   Padic Unit Ball: p mem maximal Ideal
-- statement:
--   The Padic Unit Ball construction uses the p mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L31-L45

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
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem GlobalTheory.PadicUnitBall.p_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by sorry
