-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_mono
-- name    : GlobalTheory.QCoh.topologicalKrullDim_mono
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:24.545178+00:00
-- url     : https://prove2.me/theorems/75164c74-d66a-59d9-b445-55ac651f13d7
-- title:
--   QCoh: topological Krull Dim mono
-- statement:
--   The QCoh construction uses the topological Krull Dim mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L668-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L668-L670

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

theorem GlobalTheory.QCoh.topologicalKrullDim_mono {T : Type*} [TopologicalSpace T] {s t : Set T} (h : s ⊆ t) :
    topologicalKrullDim s ≤ topologicalKrullDim t := by sorry
