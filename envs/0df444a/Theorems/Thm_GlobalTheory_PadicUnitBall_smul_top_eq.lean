-- Prove2me | Theorems.Thm_GlobalTheory_PadicUnitBall_smul_top_eq
-- name    : GlobalTheory.PadicUnitBall.smul_top_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:51.715806+00:00
-- url     : https://prove2.me/theorems/cb48ef55-f68b-417e-9d86-d5a174458a62
-- title:
--   Padic Unit Ball: smul top eq
-- statement:
--   The Padic Unit Ball construction uses the smul top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicMemRangeCompleteDvrPadicAlgCl.lean#L69-L70

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

theorem GlobalTheory.PadicUnitBall.smul_top_eq (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by sorry
