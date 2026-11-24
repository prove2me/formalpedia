-- Prove2me | Theorems.Thm_GlobalTheory_relLength_map_mkQ
-- name    : GlobalTheory.relLength_map_mkQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:48.319294+00:00
-- url     : https://prove2.me/theorems/24c82925-376c-4eed-ac93-30608ff5a2b9
-- title:
--   Global Theory: rel Length map mk Q
-- statement:
--   The Global Theory construction uses the rel Length map mk Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L242-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem GlobalTheory.relLength_map_mkQ {N B : Submodule R V} (h : N ≤ B) (A : Submodule R V) :
    relLength (A.map N.mkQ) (B.map N.mkQ) = relLength A B := by sorry
