-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_moduleOfRingHom_smul
-- name    : GlobalTheory.cohOn.moduleOfRingHom_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:24.86365+00:00
-- url     : https://prove2.me/theorems/eddc59a4-abba-4425-aba8-39995aaa29e6
-- title:
--   coh On: module Of Ring Hom smul
-- statement:
--   The coh On construction uses the module Of Ring Hom smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L223-L226

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
open GlobalTheory.cohOn

theorem GlobalTheory.cohOn.moduleOfRingHom_smul {R : Type v} [CommRing R] (f : R →+* Γ(X, ⊤)) {F : X.Modules}
    {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    letI := moduleOfRingHom f F U n
    r • x = f r • x := by sorry
