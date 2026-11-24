-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Mram_ne_bot
-- name    : GlobalTheory.LatPair.Mram_ne_bot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:31.154858+00:00
-- url     : https://prove2.me/theorems/50172acf-47a9-46eb-9ec8-e9d6715b1d31
-- title:
--   Lat Pair: Mram ne bot
-- statement:
--   The Lat Pair construction uses the Mram ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L640-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L640-L647

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

theorem GlobalTheory.LatPair.Mram_ne_bot [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) : Mram k n ℂ ≠ ⊥ := by sorry
