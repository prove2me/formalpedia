-- Prove2me | Theorems.Thm_GlobalTheory_hdim_eq_zero_of_subsingleton
-- name    : GlobalTheory.hdim_eq_zero_of_subsingleton
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:26:22.032886+00:00
-- url     : https://prove2.me/theorems/3f4e8958-bd4a-4e0f-b9a6-a77fa4d4c0c3
-- title:
--   Global Theory: hdim eq zero of subsingleton
-- statement:
--   The Global Theory construction uses the hdim eq zero of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L593-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L593-L594

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

theorem GlobalTheory.hdim_eq_zero_of_subsingleton [Subsingleton (coh F n)] : hdim k F n = 0 := by sorry
