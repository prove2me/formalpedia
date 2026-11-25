-- Prove2me | Theorems.Thm_GlobalTheory_smulHom_eq_smul_id
-- name    : GlobalTheory.smulHom_eq_smul_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:55.737774+00:00
-- url     : https://prove2.me/theorems/d82a924e-0cb2-486c-b1f2-10cbb2722992
-- title:
--   Global Theory: smul Hom eq smul id
-- statement:
--   The Global Theory construction uses the smul Hom eq smul id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L104-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}

theorem GlobalTheory.smulHom_eq_smul_id (F : X.Modules) (r : Γ(X, ⊤)) : smulHom F r = r • 𝟙 F := by sorry
