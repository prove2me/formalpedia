-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_LatBij_diag_unit_mem
-- name    : GlobalTheory.CMVal.LatBij.diag_unit_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:55.44746+00:00
-- url     : https://prove2.me/theorems/5a42d156-fcb6-4f7e-915d-a55386173dfa
-- title:
--   Lat Bij: diag unit mem
-- statement:
--   The Lat Bij construction uses the diag unit mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L21-L24

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

theorem GlobalTheory.CMVal.LatBij.diag_unit_mem (c : Ideal (OF E)) (u : (OF E)ˣ) :
    diag (Units.map (algebraMap (OF E) E).toMonoidHom u) ∈ hatOUnits c := by sorry
