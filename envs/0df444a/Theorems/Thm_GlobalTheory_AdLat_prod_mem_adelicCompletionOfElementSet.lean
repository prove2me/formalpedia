-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_prod_mem_adelicCompletionOfElementSet
-- name    : GlobalTheory.AdLat.prod_mem_adelicCompletionOfElementSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:43.898521+00:00
-- url     : https://prove2.me/theorems/f7a230b4-0a54-44cd-aa6a-1d2d61465e22
-- title:
--   Ad Lat: prod mem adelic Completion Of Element Set
-- statement:
--   The Ad Lat construction uses the prod mem adelic Completion Of Element Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L16-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.AdLat.prod_mem_adelicCompletionOfElementSet {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (x : ι → RA F E) (h : ∀ i ∈ s, x i ∈ hat1 F (I i : Set E)) :
    ∏ i ∈ s, x i ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by sorry
