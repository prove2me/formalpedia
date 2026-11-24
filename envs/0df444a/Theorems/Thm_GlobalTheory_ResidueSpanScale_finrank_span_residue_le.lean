-- Prove2me | Theorems.Thm_GlobalTheory_ResidueSpanScale_finrank_span_residue_le
-- name    : GlobalTheory.ResidueSpanScale.finrank_span_residue_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:17.91018+00:00
-- url     : https://prove2.me/theorems/ae891f9a-c8e0-49a7-94ea-d460ace6b36b
-- title:
--   Residue Span Scale: finrank span residue le
-- statement:
--   The Residue Span Scale construction uses the finrank span residue le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankSpanResidueLe.lean#L27-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankSpanResidueLe.lean#L27-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankSpanResidueLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ResidueSpanScale

theorem GlobalTheory.ResidueSpanScale.finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by sorry
