-- Prove2me | Theorems.Thm_GlobalTheory_PadicUnitBall_exists_norm_le_pow
-- name    : GlobalTheory.PadicUnitBall.exists_norm_le_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:45.421101+00:00
-- url     : https://prove2.me/theorems/dc5fee1c-bb37-400e-b378-d4658631e04f
-- title:
--   Padic Unit Ball: exists norm le pow
-- statement:
--   The Padic Unit Ball construction uses the exists norm le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L54-L67

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

theorem GlobalTheory.PadicUnitBall.exists_norm_le_pow
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by sorry
