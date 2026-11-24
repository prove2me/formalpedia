-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_not_mem_int_of_ne
-- name    : GlobalTheory.HeisUnit.not_mem_int_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:48.118811+00:00
-- url     : https://prove2.me/theorems/e2a83308-145a-4a39-b0b9-f0ad295045d5
-- title:
--   Heis Unit: not mem int of ne
-- statement:
--   The Heis Unit construction uses the not mem int of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergCosetRepTranslatesOrthogonal.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergCosetRepTranslatesOrthogonal.lean#L66-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit

theorem GlobalTheory.HeisUnit.not_mem_int_of_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : SplitFlip.IsUnif ϖ) (t t' : SplitFlip.Res k 1) (h : t ≠ t') :
    (ϖ : k)⁻¹ * (((Quotient.out t : 𝒪[k]) : k) - ((Quotient.out t' : 𝒪[k]) : k)) ∉ 𝒪[k] := by sorry
