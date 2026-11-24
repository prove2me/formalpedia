-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_intInd_diagAt_eq_sum
-- name    : GlobalTheory.HeisUnit.intInd_diagAt_eq_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:17:49.967878+00:00
-- url     : https://prove2.me/theorems/fbe0054e-e1a4-42e1-975b-58fa51aea179
-- title:
--   Heis Unit: int Ind diag At eq sum
-- statement:
--   The Heis Unit construction uses the int Ind diag At eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L44-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubInvMulOutMemIff.lean#L44-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubInvMulOutMemIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.HeisUnit.intInd_diagAt_eq_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (Y : Matrix (Fin n) (Fin d) k),
    GlobalTheory.HeisUnit.intInd k n d ((GlobalTheory.HeisUnit.diagAt ϖ i0).valᵀ * Y) =
      ∑ T : Fin d → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.HeisUnit.intInd k n d (Y + GlobalTheory.HeisUnit.cosetRep ϖ i0 T) := by sorry
