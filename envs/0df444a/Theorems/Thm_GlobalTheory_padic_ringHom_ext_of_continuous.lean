-- Prove2me | Theorems.Thm_GlobalTheory_padic_ringHom_ext_of_continuous
-- name    : GlobalTheory.padic_ringHom_ext_of_continuous
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:16.946023+00:00
-- url     : https://prove2.me/theorems/e64a0bc3-501a-548d-85c8-bb99a2daa34b
-- title:
--   Global Theory: padic ring Hom ext of continuous
-- statement:
--   The Global Theory construction uses the padic ring Hom ext of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L442-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L442-L446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.padic_ringHom_ext_of_continuous {C : Type*} [NormedField C] (p : ℕ) [Fact p.Prime]
    {j₁ j₂ : ℚ_[p] →+* C} (h₁ : Continuous j₁) (h₂ : Continuous j₂) : j₁ = j₂ := by sorry
