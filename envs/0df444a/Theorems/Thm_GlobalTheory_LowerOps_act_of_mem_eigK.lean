-- Prove2me | Theorems.Thm_GlobalTheory_LowerOps_act_of_mem_eigK
-- name    : GlobalTheory.LowerOps.act_of_mem_eigK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:02.519019+00:00
-- url     : https://prove2.me/theorems/f207e844-b9ab-42df-88a4-2a56e17f6fa1
-- title:
--   Lower Ops: act of mem eig K
-- statement:
--   The Lower Ops construction uses the act of mem eig K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.LowerOps.act_of_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {x : K ⊗[O] H}
    (hx : x ∈ eigK ρ σ) (a : orderC c) : (ρ a).baseChange K x = σ a • x := by sorry
