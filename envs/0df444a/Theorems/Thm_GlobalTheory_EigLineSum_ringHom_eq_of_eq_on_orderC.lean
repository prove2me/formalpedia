-- Prove2me | Theorems.Thm_GlobalTheory_EigLineSum_ringHom_eq_of_eq_on_orderC
-- name    : GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:15.964941+00:00
-- url     : https://prove2.me/theorems/3401b260-8723-476e-80a3-a8f0cdbb3bd8
-- title:
--   Eig Line Sum: ring Hom eq of eq on order C
-- statement:
--   The Eig Line Sum construction uses the ring Hom eq of eq on order C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFirst.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFirst.lean#L10-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFirst
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
open GlobalTheory GlobalTheory.EigLineSum

theorem GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    {c : Ideal (OF E)} (hc : c ≠ ⊥) {σ σ' : E →+* K} (h : ∀ a : orderC c, σ a = σ' a) : σ = σ' := by sorry
