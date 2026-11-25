-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mem_support_iff_annihilator_le
-- name    : GlobalTheory.QCoh.mem_support_iff_annihilator_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:44.532388+00:00
-- url     : https://prove2.me/theorems/beb9baea-90bf-5de0-a72c-39122b3f89c0
-- title:
--   QCoh: mem support iff annihilator le
-- statement:
--   The QCoh construction uses the mem support iff annihilator le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L461-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L461-L465

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

theorem GlobalTheory.QCoh.mem_support_iff_annihilator_le [IsFiniteQC F] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support F ↔
      Module.annihilator Γ(X, U) Γ(F, U) ≤ (hU.primeIdealOf x).asIdeal := by sorry
