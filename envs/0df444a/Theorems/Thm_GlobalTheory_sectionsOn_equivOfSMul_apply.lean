-- Prove2me | Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- name    : GlobalTheory.sectionsOn.equivOfSMul_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:31.935368+00:00
-- url     : https://prove2.me/theorems/dbdd29a2-6fce-47c0-a5ac-72a5f604b04b
-- title:
--   sections On: equiv Of SMul apply
-- statement:
--   The sections On construction uses the equiv Of SMul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L409-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L409-L411

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

theorem GlobalTheory.sectionsOn.equivOfSMul_apply [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x)
    (x : sectionsOn F U) : equivOfSMul R F U h x = toΓ F U x := by sorry

attribute [defeq] GlobalTheory.sectionsOn.equivOfSMul_apply
