-- Prove2me | Theorems.Thm_GlobalTheory_restrictGlobal_top
-- name    : GlobalTheory.restrictGlobal_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:46.232998+00:00
-- url     : https://prove2.me/theorems/2a1850cd-d0cf-4c80-a25f-79bb0a9f6ce3
-- title:
--   Global Theory: restrict Global top
-- statement:
--   The Global Theory construction uses the restrict Global top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L39-L42

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

theorem GlobalTheory.restrictGlobal_top (r : Γ(X, ⊤)) : restrictGlobal X ⊤ r = r := by sorry
