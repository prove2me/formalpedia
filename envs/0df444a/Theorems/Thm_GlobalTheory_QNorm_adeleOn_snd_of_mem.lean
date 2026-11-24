-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_mem
-- name    : GlobalTheory.QNorm.adeleOn_snd_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:08.274492+00:00
-- url     : https://prove2.me/theorems/ba61621e-5f58-435a-a771-b53e38e3c10c
-- title:
--   QNorm: adele On snd of mem
-- statement:
--   The QNorm construction uses the adele On snd of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L48-L50

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

theorem GlobalTheory.QNorm.adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := by sorry
