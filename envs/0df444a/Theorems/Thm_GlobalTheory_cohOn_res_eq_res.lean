-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_res_eq_res
-- name    : GlobalTheory.cohOn.res_eq_res
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:21.267623+00:00
-- url     : https://prove2.me/theorems/da8158a2-e590-4441-af93-f5f22e4db94f
-- title:
--   coh On: res eq res
-- statement:
--   The coh On construction uses the res eq res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L101-L102

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
variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}

theorem GlobalTheory.cohOn.res_eq_res (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (h : V ≤ U) (x : cohOn F U n) :
    res R F h n x = res S F h n x := by sorry
