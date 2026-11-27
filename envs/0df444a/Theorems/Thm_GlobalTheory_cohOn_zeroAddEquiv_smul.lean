-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_zeroAddEquiv_smul
-- name    : GlobalTheory.cohOn.zeroAddEquiv_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:35.653553+00:00
-- url     : https://prove2.me/theorems/322a9057-3d9e-4b13-ab69-77c34760a652
-- title:
--   coh On: zero Add Equiv smul
-- statement:
--   The coh On construction uses the zero Add Equiv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L455-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L455-L457

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
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G : X.Modules} {U V : X.Opens}

theorem GlobalTheory.cohOn.zeroAddEquiv_smul (r : R) (x : cohOn F U 0) :
    zeroAddEquiv F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • zeroAddEquiv F U x := by sorry
