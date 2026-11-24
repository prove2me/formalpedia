-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_notMem
-- name    : GlobalTheory.QNorm.adeleOn_snd_of_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:09:07.800435+00:00
-- url     : https://prove2.me/theorems/8f3405ab-8de8-42a5-9fb9-0823e89d7f76
-- title:
--   QNorm: adele On snd of not Mem
-- statement:
--   The QNorm construction uses the adele On snd of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L52-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := by sorry
