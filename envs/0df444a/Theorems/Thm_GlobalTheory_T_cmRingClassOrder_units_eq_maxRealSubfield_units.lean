-- Prove2me | Theorems.Thm_GlobalTheory_T_cmRingClassOrder_units_eq_maxRealSubfield_units
-- name    : GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:53.597949+00:00
-- url     : https://prove2.me/theorems/f07fdcde-57e8-47d0-a4d8-f0a0ee8f9508
-- title:
--   T: cm Ring Class Order units eq max Real Subfield units
-- statement:
--   The T construction uses the cm Ring Class Order units eq max Real Subfield units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by sorry
