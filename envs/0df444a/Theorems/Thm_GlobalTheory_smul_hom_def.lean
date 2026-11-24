-- Prove2me | Theorems.Thm_GlobalTheory_smul_hom_def
-- name    : GlobalTheory.smul_hom_def
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:30.039973+00:00
-- url     : https://prove2.me/theorems/2ec4dd2e-9273-4140-afd1-27591ced48ff
-- title:
--   Global Theory: smul hom def
-- statement:
--   The Global Theory construction uses the smul hom def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L102-L102

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

theorem GlobalTheory.smul_hom_def {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) : r • φ = φ ≫ smulHom G r := by sorry
