-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
-- name    : GlobalTheory.LatPair.Model.sum_stable_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:21.421811+00:00
-- url     : https://prove2.me/theorems/150c0951-8d88-4e29-ada5-9f34fbdf509e
-- title:
--   Model: sum stable eq zero
-- statement:
--   The Model construction uses the sum stable eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L103-L112

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

theorem GlobalTheory.LatPair.Model.sum_stable_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) (s : Finset (Pair k n))
    (hs : ∀ (c : 𝓀[k]ˣ) P, c • P ∈ s ↔ P ∈ s) : ∑ P ∈ s, φ P = 0 := by sorry
