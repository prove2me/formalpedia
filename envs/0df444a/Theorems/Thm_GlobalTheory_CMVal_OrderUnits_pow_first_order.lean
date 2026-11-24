-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_pow_first_order
-- name    : GlobalTheory.CMVal.OrderUnits.pow_first_order
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:05.233061+00:00
-- url     : https://prove2.me/theorems/7f46d08f-4c0c-449d-8baf-1953c231ef07
-- title:
--   Order Units: pow first order
-- statement:
--   The Order Units construction uses the pow first order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L39-L44

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits

theorem GlobalTheory.CMVal.OrderUnits.pow_first_order {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by sorry
