-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_of_mem_hatO
-- name    : GlobalTheory.CMVal.Euler.locIn_of_mem_hatO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:11.783476+00:00
-- url     : https://prove2.me/theorems/bf091f7c-7c15-487d-9127-ba468544c2ab
-- title:
--   Euler: loc In of mem hat O
-- statement:
--   The Euler construction uses the loc In of mem hat O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L139-L143

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.locIn_of_mem_hatO {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (v : HeightOneSpectrum (OF E)) :
    LocIn (expIn c v) v z := by sorry
