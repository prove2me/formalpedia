-- Prove2me | Theorems.Thm_GlobalTheory_sectionsOn_res_map
-- name    : GlobalTheory.sectionsOn.res_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:45.022901+00:00
-- url     : https://prove2.me/theorems/8ff2ef58-2ffb-477a-94b7-4e074e1df271
-- title:
--   sections On: res map
-- statement:
--   The sections On construction uses the res map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L398-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L398-L400

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
open GlobalTheory.sectionsOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G H : X.Modules} {U V W : X.Opens}

theorem GlobalTheory.sectionsOn.res_map (φ : F ⟶ G) (h : V ≤ U) (x : sectionsOn F U) :
    res R G h (map R φ U x) = map R φ V (res R F h x) := by sorry
