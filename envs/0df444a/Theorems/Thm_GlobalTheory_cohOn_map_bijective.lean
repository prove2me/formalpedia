-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_map_bijective
-- name    : GlobalTheory.cohOn.map_bijective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:59.24867+00:00
-- url     : https://prove2.me/theorems/2e3bae7d-3bad-5702-ad54-7f756d468e7c
-- title:
--   coh On: map bijective
-- statement:
--   The coh On construction uses the map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L207-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L207-L208

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

theorem GlobalTheory.cohOn.map_bijective (φ : F ⟶ G) [IsIso φ] : Function.Bijective (map R φ U n) := by sorry
