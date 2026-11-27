-- Prove2me | Theorems.Thm_GlobalTheory_coh_toH_map
-- name    : GlobalTheory.coh.toH_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:55.324448+00:00
-- url     : https://prove2.me/theorems/45d6c054-6e2a-5b13-8348-f4b7c60d84c8
-- title:
--   coh: to H map
-- statement:
--   The coh construction uses the to H map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L488-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L488-L491

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
open GlobalTheory.coh

theorem GlobalTheory.coh.toH_map (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : coh F n) :
    toH G n (cohOn.map R φ ⊤ n x) = Sheaf.H.map ((toAbSheaf X).map φ) n (toH F n x) := by sorry
