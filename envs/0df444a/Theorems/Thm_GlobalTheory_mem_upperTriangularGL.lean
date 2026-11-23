-- Prove2me | Theorems.Thm_GlobalTheory_mem_upperTriangularGL
-- name    : GlobalTheory.mem_upperTriangularGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:35.048172+00:00
-- url     : https://prove2.me/theorems/7ad93da7-27be-4db4-8bab-24af184246d8
-- title:
--   Global Theory: mem upper Triangular GL
-- statement:
--   The Global Theory construction uses the mem upper Triangular GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L116-L118

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

theorem GlobalTheory.mem_upperTriangularGL {g : GL ι R} :
    g ∈ upperTriangularGL ι R ↔ ∀ i j, j < i → (g : Matrix ι ι R) i j = 0 := by sorry
