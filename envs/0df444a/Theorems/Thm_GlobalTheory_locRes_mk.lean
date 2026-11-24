-- Prove2me | Theorems.Thm_GlobalTheory_locRes_mk
-- name    : GlobalTheory.locRes_mk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:49.353825+00:00
-- url     : https://prove2.me/theorems/7e62c20a-84c1-481c-9098-40f86efc8ab1
-- title:
--   Global Theory: loc Res mk
-- statement:
--   The Global Theory construction uses the loc Res mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L240-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L240-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]

theorem GlobalTheory.locRes_mk {s t : Finset ι} (h : s ⊆ t) (m : M) (a : Submonoid.powers (∏ i ∈ s, f i))
    (b : Submonoid.powers (∏ i ∈ t, f i)) (c : R) (hb : (b : R) = c * a) :
    locRes f M h (LocalizedModule.mk m a) = LocalizedModule.mk (c • m) b := by sorry
