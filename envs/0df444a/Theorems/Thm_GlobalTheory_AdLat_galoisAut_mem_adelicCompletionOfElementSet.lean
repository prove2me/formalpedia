-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_galoisAut_mem_adelicCompletionOfElementSet
-- name    : GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:45.424808+00:00
-- url     : https://prove2.me/theorems/baa39758-9a0b-4906-b8cd-028002b3ad76
-- title:
--   Ad Lat: galois Aut mem adelic Completion Of Element Set
-- statement:
--   The Ad Lat construction uses the galois Aut mem adelic Completion Of Element Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L68-L76

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

theorem GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by sorry
