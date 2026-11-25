-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fibreMap_exact
-- name    : GlobalTheory.QCoh.fibreMap_exact
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:16.776832+00:00
-- url     : https://prove2.me/theorems/d6bea3aa-cd2a-4ef2-b481-c3c9cb30782d
-- title:
--   QCoh: fibre Map exact
-- statement:
--   The QCoh construction uses the fibre Map exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1118-L1120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1118-L1120

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

theorem GlobalTheory.QCoh.fibreMap_exact {S : ShortComplex X.Modules} (hS : S.Exact) [Epi S.g] (x : X) :
    Function.Exact (fibreMap S.f x) (fibreMap S.g x) := by sorry
