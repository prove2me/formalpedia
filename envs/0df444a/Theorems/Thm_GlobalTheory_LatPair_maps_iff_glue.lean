-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_maps_iff_glue
-- name    : GlobalTheory.LatPair.maps_iff_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:36.410832+00:00
-- url     : https://prove2.me/theorems/6c4349e8-0efa-4b6d-8183-bdcd694d332f
-- title:
--   Lat Pair: maps iff glue
-- statement:
--   The Lat Pair construction uses the maps iff glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L344-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L344-L350

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

theorem GlobalTheory.LatPair.maps_iff_glue {e : n' → k} {e' : n → k} (he : P.HasVal e 1) (he' : Q.HasVal e' 1) :
    Maps P Q x ↔ (∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker) ∧ x *ᵥ e - e' ∈ Q.ker := by sorry
