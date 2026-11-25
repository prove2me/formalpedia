-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_support_inter_eq_zeroLocus
-- name    : GlobalTheory.QCoh.support_inter_eq_zeroLocus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:30.713866+00:00
-- url     : https://prove2.me/theorems/6edfb66b-c75e-522b-b800-e3b915acca17
-- title:
--   QCoh: support inter eq zero Locus
-- statement:
--   The QCoh construction uses the support inter eq zero Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L469-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L469-L476

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
variable (F)

theorem GlobalTheory.QCoh.support_inter_eq_zeroLocus [IsFiniteQC F] (hU : IsAffineOpen U) :
    support F ∩ U = X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)) ∩ U := by sorry
