-- Prove2me | Theorems.Thm_GlobalTheory_PadicUnitBall_norm_natCast_p
-- name    : GlobalTheory.PadicUnitBall.norm_natCast_p
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:57.85357+00:00
-- url     : https://prove2.me/theorems/72a86614-f8b7-4725-be8e-a183f1549d7f
-- title:
--   Padic Unit Ball: norm nat Cast p
-- statement:
--   The Padic Unit Ball construction uses the norm nat Cast p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L26-L29

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

theorem GlobalTheory.PadicUnitBall.norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by sorry
