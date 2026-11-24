-- Prove2me | Theorems.Thm_GlobalTheory_hdim_pi
-- name    : GlobalTheory.hdim_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:12.176063+00:00
-- url     : https://prove2.me/theorems/225d8778-2e81-4966-a564-620d0364e787
-- title:
--   Global Theory: hdim pi
-- statement:
--   The Global Theory construction uses the hdim pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L603-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L603-L605

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

theorem GlobalTheory.hdim_pi {ι : Type t} [Fintype ι] (F : ι → X.Modules) [∀ i, Module.Finite k (coh (F i) n)] :
    hdim k (∏ᶜ F) n = ∑ i, hdim k (F i) n := by sorry
