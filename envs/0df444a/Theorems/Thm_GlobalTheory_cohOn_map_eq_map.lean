-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_map_eq_map
-- name    : GlobalTheory.cohOn.map_eq_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:25.867204+00:00
-- url     : https://prove2.me/theorems/aa5bbd55-3be8-4b7c-8994-e1b93af59e9e
-- title:
--   coh On: map eq map
-- statement:
--   The coh On construction uses the map eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L98-L99

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

theorem GlobalTheory.cohOn.map_eq_map (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (φ : F ⟶ G) (x : cohOn F U n) :
    map R φ U n x = map S φ U n x := by sorry
