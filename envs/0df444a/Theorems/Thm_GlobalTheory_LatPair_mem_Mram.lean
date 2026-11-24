-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_mem_Mram
-- name    : GlobalTheory.LatPair.mem_Mram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:59.16907+00:00
-- url     : https://prove2.me/theorems/e21b6525-4069-420e-ac57-885adaeb3c43
-- title:
--   Lat Pair: mem Mram
-- statement:
--   The Lat Pair construction uses the mem Mram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L91-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
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
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem GlobalTheory.LatPair.mem_Mram [Fintype 𝓀[k]ˣ] : φ ∈ Mram k n M ↔ ∀ P, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := by sorry
