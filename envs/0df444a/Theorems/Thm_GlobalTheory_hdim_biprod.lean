-- Prove2me | Theorems.Thm_GlobalTheory_hdim_biprod
-- name    : GlobalTheory.hdim_biprod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:24.601803+00:00
-- url     : https://prove2.me/theorems/bb5c16a4-ee06-4205-ba35-d3ca0143655f
-- title:
--   Global Theory: hdim biprod
-- statement:
--   The Global Theory construction uses the hdim biprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L599-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L599-L601

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] {F G : X.Modules} (n : ℕ)

theorem GlobalTheory.hdim_biprod [Module.Finite k (coh F n)] [Module.Finite k (coh G n)] :
    hdim k (F ⊞ G) n = hdim k F n + hdim k G n := by sorry
