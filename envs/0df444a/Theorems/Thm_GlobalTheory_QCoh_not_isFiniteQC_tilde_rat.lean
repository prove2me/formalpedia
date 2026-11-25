-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_not_isFiniteQC_tilde_rat
-- name    : GlobalTheory.QCoh.not_isFiniteQC_tilde_rat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:54.233985+00:00
-- url     : https://prove2.me/theorems/41384e6e-241a-4f51-80d0-adf164ab30ca
-- title:
--   QCoh: not is Finite QC tilde rat
-- statement:
--   The QCoh construction uses the not is Finite QC tilde rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L321-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L321-L333

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
variable {R : CommRingCat.{u}}

theorem GlobalTheory.QCoh.not_isFiniteQC_tilde_rat :
    ¬ IsFiniteQC (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ)) := by sorry
