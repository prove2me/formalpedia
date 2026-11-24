-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_mul_mem_integer_iff_of_valuation_eq_one
-- name    : GlobalTheory.HeisUnit.mul_mem_integer_iff_of_valuation_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:42.731921+00:00
-- url     : https://prove2.me/theorems/f0714147-3ea5-49ec-9571-1991b4fa9448
-- title:
--   Heis Unit: mul mem integer iff of valuation eq one
-- statement:
--   The Heis Unit construction uses the mul mem integer iff of valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCharacterUnitEqOneHeisenberg.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCharacterUnitEqOneHeisenberg.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenberg
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.HeisUnit.mul_mem_integer_iff_of_valuation_eq_one {u : kˣ} (hu : valuation k (u : k) = 1) (y : k) :
    (u : k) * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by sorry
