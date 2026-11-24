-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_orbit
-- name    : GlobalTheory.WeilM.isLocallyConstant_orbit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:05.467058+00:00
-- url     : https://prove2.me/theorems/07add075-d21f-44e6-a74f-7263f03d2ab1
-- title:
--   Weil M: is Locally Constant orbit
-- statement:
--   The Weil M construction uses the is Locally Constant orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L12-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM

theorem GlobalTheory.WeilM.isLocallyConstant_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (om : G →* Module.End ℂ V) {v : V} (h : ∀ᶠ g in 𝓝 (1 : G), om g v = v) :
    IsLocallyConstant fun g => om g v := by sorry
