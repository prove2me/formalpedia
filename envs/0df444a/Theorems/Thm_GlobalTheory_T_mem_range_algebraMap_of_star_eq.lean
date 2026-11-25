-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_range_algebraMap_of_star_eq
-- name    : GlobalTheory.T.mem_range_algebraMap_of_star_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:28.787291+00:00
-- url     : https://prove2.me/theorems/4e999450-5ff6-4cd5-846c-305643d80890
-- title:
--   T: mem range algebra Map of star eq
-- statement:
--   The T construction uses the mem range algebra Map of star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeAlgebraMapOfStarEqStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeAlgebraMapOfStarEqStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeAlgebraMapOfStarEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeAlgebraMapOfStarEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by sorry
