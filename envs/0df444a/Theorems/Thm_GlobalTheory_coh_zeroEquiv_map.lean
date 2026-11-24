-- Prove2me | Theorems.Thm_GlobalTheory_coh_zeroEquiv_map
-- name    : GlobalTheory.coh.zeroEquiv_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:16.156384+00:00
-- url     : https://prove2.me/theorems/0063769b-9a13-4ef0-aaad-154eb0cbca9c
-- title:
--   coh: zero Equiv map
-- statement:
--   The coh construction uses the zero Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L481-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L481-L483

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
open GlobalTheory.coh

theorem GlobalTheory.coh.zeroEquiv_map {F G : X.Modules} (φ : F ⟶ G) (x : coh F 0) :
    zeroEquiv G (cohOn.map Γ(X, ⊤) φ ⊤ 0 x) = φ.app ⊤ (zeroEquiv F x) := by sorry
