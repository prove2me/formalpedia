-- Prove2me | Theorems.Thm_GlobalTheory_hdim_eq_rank
-- name    : GlobalTheory.hdim_eq_rank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:21.962875+00:00
-- url     : https://prove2.me/theorems/16081519-3f19-49d6-931e-c73235e285ea
-- title:
--   Global Theory: hdim eq rank
-- statement:
--   The Global Theory construction uses the hdim eq rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L586-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L586-L588

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

theorem GlobalTheory.hdim_eq_rank [Module.Finite k (coh F n)] :
    (hdim k F n : Cardinal) = Module.rank k (coh F n) := by sorry
