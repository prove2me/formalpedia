-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_LatBij_coe_diag
-- name    : GlobalTheory.CMVal.LatBij.coe_diag
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:47.728172+00:00
-- url     : https://prove2.me/theorems/30af21d6-3c76-49dd-9745-995be84ff1ee
-- title:
--   Lat Bij: coe diag
-- statement:
--   The Lat Bij construction uses the coe diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L17-L17

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.LatBij.coe_diag (a : Eˣ) : (diag a : Af E) = algebraMap E (Af E) a := by sorry
