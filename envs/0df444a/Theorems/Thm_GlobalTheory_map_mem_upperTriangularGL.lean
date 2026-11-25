-- Prove2me | Theorems.Thm_GlobalTheory_map_mem_upperTriangularGL
-- name    : GlobalTheory.map_mem_upperTriangularGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:08.255279+00:00
-- url     : https://prove2.me/theorems/ce761634-3182-59d2-9fa6-3ecca5ccaba5
-- title:
--   Global Theory: map mem upper Triangular GL
-- statement:
--   The Global Theory construction uses the map mem upper Triangular GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L137-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}

theorem GlobalTheory.map_mem_upperTriangularGL {S : Type*} [CommRing S] (f : R →+* S) {g : GL ι R}
    (hg : g ∈ upperTriangularGL ι R) :
    Matrix.GeneralLinearGroup.map f g ∈ upperTriangularGL ι S := by sorry
