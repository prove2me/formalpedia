-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_div_mem_normSub
-- name    : GlobalTheory.QNorm.div_mem_normSub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:00.694732+00:00
-- url     : https://prove2.me/theorems/60a64cc8-7ea0-421f-8696-37d49de2829b
-- title:
--   QNorm: div mem norm Sub
-- statement:
--   The QNorm construction uses the div mem norm Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNorm.lean#L68-L73

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

theorem GlobalTheory.QNorm.div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by sorry
