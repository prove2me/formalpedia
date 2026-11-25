-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_shortExact
-- name    : GlobalTheory.QCoh.IsFiniteQC.of_shortExact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:28.202009+00:00
-- url     : https://prove2.me/theorems/881af4ef-c6cf-506d-991c-d20297d859f9
-- title:
--   Is Finite QC: of short Exact
-- statement:
--   The Is Finite QC construction uses the of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L125-L132

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
attribute [instance 100] IsFiniteQC.isQuasicoherent

theorem GlobalTheory.QCoh.IsFiniteQC.of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteQC S.X₁] [S.X₂.IsQuasicoherent] [IsFiniteQC S.X₃] : IsFiniteQC S.X₂ := by sorry
