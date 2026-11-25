-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_map_sub_hom
-- name    : GlobalTheory.cohOn.map_sub_hom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:19.254197+00:00
-- url     : https://prove2.me/theorems/035d7cca-0cb2-4225-a33d-50e92c35915d
-- title:
--   coh On: map sub hom
-- statement:
--   The coh On construction uses the map sub hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L153-L154

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
variable (U n)

theorem GlobalTheory.cohOn.map_sub_hom (φ ψ : F ⟶ G) : map R (φ - ψ) U n = map R φ U n - map R ψ U n := by sorry
