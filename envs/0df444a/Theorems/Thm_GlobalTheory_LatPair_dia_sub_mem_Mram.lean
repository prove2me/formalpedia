-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_dia_sub_mem_Mram
-- name    : GlobalTheory.LatPair.dia_sub_mem_Mram
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:33.843327+00:00
-- url     : https://prove2.me/theorems/3b4f26ac-888b-4beb-803d-cbc743d7c097
-- title:
--   Lat Pair: dia sub mem Mram
-- statement:
--   The Lat Pair construction uses the dia sub mem Mram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L147-L151

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

theorem GlobalTheory.LatPair.dia_sub_mem_Mram (c : 𝓀[k]ˣ) : dia c φ - φ ∈ Mram k n M := by sorry
