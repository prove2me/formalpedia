-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isSMulRegular_sections_iff
-- name    : GlobalTheory.QCoh.isSMulRegular_sections_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:33.788676+00:00
-- url     : https://prove2.me/theorems/149d21aa-78df-5815-8ba5-7671114ec231
-- title:
--   QCoh: is SMul Regular sections iff
-- statement:
--   The QCoh construction uses the is SMul Regular sections iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L933-L950
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L933-L950

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
variable [IsLocallyNoetherian X]

theorem GlobalTheory.QCoh.isSMulRegular_sections_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsSMulRegular Γ(F, U) f ↔ assPoints F ∩ U ⊆ X.basicOpen f := by sorry
