-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_sum_char
-- name    : GlobalTheory.LatPair.Model.sum_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:00.800015+00:00
-- url     : https://prove2.me/theorems/008460db-f71b-4251-8e53-874b5c6c2927
-- title:
--   Model: sum char
-- statement:
--   The Model construction uses the sum char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L69-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.LatPair.Model.sum_char {V : Type*} [AddCommGroup V] [Module 𝓀[k] V] [Fintype V] {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1)
    (g : Module.Dual 𝓀[k] V) [Decidable (g = 0)] : ∑ x, χ (g x) = if g = 0 then (Fintype.card V : ℂ) else 0 := by sorry
