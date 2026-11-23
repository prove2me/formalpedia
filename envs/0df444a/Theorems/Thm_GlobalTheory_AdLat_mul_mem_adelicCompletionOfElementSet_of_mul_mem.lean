-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
-- name    : GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:19.414143+00:00
-- url     : https://prove2.me/theorems/2428c35c-97fb-4f20-b7f9-02f01f31cd78
-- title:
--   Ad Lat: mul mem adelic Completion Of Element Set of mul mem
-- statement:
--   The Ad Lat construction uses the mul mem adelic Completion Of Element Set of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L50-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by sorry
