-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_eq_bot_iff
-- name    : GlobalTheory.QCoh.topologicalKrullDim_eq_bot_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:28.83221+00:00
-- url     : https://prove2.me/theorems/eaeea243-a45a-4cd5-9257-6d8ba2955fb5
-- title:
--   QCoh: topological Krull Dim eq bot iff
-- statement:
--   The QCoh construction uses the topological Krull Dim eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L703-L707
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L703-L707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}

theorem GlobalTheory.QCoh.topologicalKrullDim_eq_bot_iff {T : Type*} [TopologicalSpace T] :
    topologicalKrullDim T = ⊥ ↔ IsEmpty T := by sorry
