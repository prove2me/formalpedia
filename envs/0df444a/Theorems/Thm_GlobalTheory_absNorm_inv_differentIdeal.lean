-- Prove2me | Theorems.Thm_GlobalTheory_absNorm_inv_differentIdeal
-- name    : GlobalTheory.absNorm_inv_differentIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:38.655011+00:00
-- url     : https://prove2.me/theorems/7bd45d89-a327-4311-a470-2b7e5b242481
-- title:
--   Global Theory: abs Norm inv different Ideal
-- statement:
--   The Global Theory construction uses the abs Norm inv different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L117-L121

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
variable {K : Type*} [Field K] [NumberField K]
variable (K)

theorem GlobalTheory.absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by sorry
