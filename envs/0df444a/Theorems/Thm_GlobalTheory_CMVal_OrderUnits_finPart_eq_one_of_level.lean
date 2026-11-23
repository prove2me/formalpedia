-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_finPart_eq_one_of_level
-- name    : GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:33.948626+00:00
-- url     : https://prove2.me/theorems/e29031ab-b9b5-406a-9a63-26dfa3b0cf4a
-- title:
--   Order Units: fin Part eq one of level
-- statement:
--   The Order Units construction uses the fin Part eq one of level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L92-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L92-L137

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by sorry
