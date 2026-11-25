-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_zeroEquiv_res
-- name    : GlobalTheory.cohOn.zeroEquiv_res
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:32.070794+00:00
-- url     : https://prove2.me/theorems/f8d3c220-c9d4-403d-9102-a0752fa83fa8
-- title:
--   coh On: zero Equiv res
-- statement:
--   The coh On construction uses the zero Equiv res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L446-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L446-L448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_res

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

theorem GlobalTheory.cohOn.zeroEquiv_res (h : V ≤ U) (x : cohOn F U 0) :
    zeroEquiv R F V (res R F h 0 x) = sectionsOn.res R F h (zeroEquiv R F U x) := by sorry
