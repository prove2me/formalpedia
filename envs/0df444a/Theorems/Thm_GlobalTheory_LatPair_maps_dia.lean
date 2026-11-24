-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_maps_dia
-- name    : GlobalTheory.LatPair.maps_dia
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:36.278048+00:00
-- url     : https://prove2.me/theorems/3e5555b4-af39-4618-8bb0-3fd24d6a0bb5
-- title:
--   Lat Pair: maps dia
-- statement:
--   The Lat Pair construction uses the maps dia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L352-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L352-L354

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
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}

theorem GlobalTheory.LatPair.maps_dia (c : 𝓀[k]ˣ) : Maps (c • P) (c • Q) x ↔ Maps P Q x := by sorry
