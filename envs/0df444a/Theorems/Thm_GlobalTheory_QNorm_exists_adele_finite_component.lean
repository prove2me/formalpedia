-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_adele_finite_component
-- name    : GlobalTheory.QNorm.exists_adele_finite_component
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:20.930521+00:00
-- url     : https://prove2.me/theorems/bdcc69f9-14b3-4a86-b15b-2a11e77a23cf
-- title:
--   QNorm: exists adele finite component
-- statement:
--   The QNorm construction uses the exists adele finite component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L9-L17

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

theorem GlobalTheory.QNorm.exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t := by sorry
