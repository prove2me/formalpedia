-- Prove2me | Theorems.Thm_GlobalTheory_bijective_ofRealHom_comp
-- name    : GlobalTheory.bijective_ofRealHom_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:04.019846+00:00
-- url     : https://prove2.me/theorems/e8237781-5963-415e-a013-a86766b101e3
-- title:
--   Global Theory: bijective of Real Hom comp
-- statement:
--   The Global Theory construction uses the bijective of Real Hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L187-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
omit [NumberField F]
variable (F)

theorem GlobalTheory.bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by sorry
