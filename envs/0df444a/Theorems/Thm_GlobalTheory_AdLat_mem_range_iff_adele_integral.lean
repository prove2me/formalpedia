-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_mem_range_iff_adele_integral
-- name    : GlobalTheory.AdLat.mem_range_iff_adele_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:10.155797+00:00
-- url     : https://prove2.me/theorems/028790f2-9d48-4abe-8b9e-914d03020ead
-- title:
--   Ad Lat: mem range iff adele integral
-- statement:
--   The Ad Lat construction uses the mem range iff adele integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L78-L86

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

theorem GlobalTheory.AdLat.mem_range_iff_adele_integral (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by sorry
