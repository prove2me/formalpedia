-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_zeroEquiv_map
-- name    : GlobalTheory.cohOn.zeroEquiv_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:13.052981+00:00
-- url     : https://prove2.me/theorems/d8b745d8-cdfa-4510-9f0a-54196c116327
-- title:
--   coh On: zero Equiv map
-- statement:
--   The coh On construction uses the zero Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L442-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L442-L444

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_map

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

theorem GlobalTheory.cohOn.zeroEquiv_map (φ : F ⟶ G) (x : cohOn F U 0) :
    zeroEquiv R G U (map R φ U 0 x) = sectionsOn.map R φ U (zeroEquiv R F U x) := by sorry
