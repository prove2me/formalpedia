-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_res_comp_map
-- name    : GlobalTheory.cohOn.res_comp_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:29.099679+00:00
-- url     : https://prove2.me/theorems/e23cf83e-2369-407e-9638-c508c4046f5b
-- title:
--   coh On: res comp map
-- statement:
--   The coh On construction uses the res comp map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L195-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L195-L197

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
variable (n)

theorem GlobalTheory.cohOn.res_comp_map (φ : F ⟶ G) (h : V ≤ U) :
    res R G h n ∘ₗ map R φ U n = map R φ V n ∘ₗ res R F h n := by sorry
