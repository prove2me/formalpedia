-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_infiniteAdele_real_component
-- name    : GlobalTheory.QNorm.exists_infiniteAdele_real_component
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:04:22.916248+00:00
-- url     : https://prove2.me/theorems/90293392-aa15-4a54-a625-5964c3ce4099
-- title:
--   QNorm: exists infinite Adele real component
-- statement:
--   The QNorm construction uses the exists infinite Adele real component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L19-L35

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

theorem GlobalTheory.QNorm.exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by sorry
