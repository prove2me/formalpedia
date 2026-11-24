-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_HatCap_mem_orderC_of_mem_hatO
-- name    : GlobalTheory.CMVal.HatCap.mem_orderC_of_mem_hatO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:06.599008+00:00
-- url     : https://prove2.me/theorems/948159d1-a6fb-4ba0-8e3b-7c41e4913d7a
-- title:
--   Hat Cap: mem order C of mem hat O
-- statement:
--   The Hat Cap construction uses the mem order C of mem hat O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L20-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L20-L45

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.HatCap
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.HatCap.mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by sorry
