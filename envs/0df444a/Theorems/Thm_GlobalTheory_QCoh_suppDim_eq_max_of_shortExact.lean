-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_suppDim_eq_max_of_shortExact
-- name    : GlobalTheory.QCoh.suppDim_eq_max_of_shortExact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:00.575476+00:00
-- url     : https://prove2.me/theorems/608726c8-e8ea-5676-90d1-ca3d5ef5a8a1
-- title:
--   QCoh: supp Dim eq max of short Exact
-- statement:
--   The QCoh construction uses the supp Dim eq max of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L737-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L737-L740

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

theorem GlobalTheory.QCoh.suppDim_eq_max_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteQC S.X₁] [IsFiniteQC S.X₃] : suppDim S.X₂ = max (suppDim S.X₁) (suppDim S.X₃) := by sorry
