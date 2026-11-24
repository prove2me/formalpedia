-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_det_mem_adelicCompletionOfElementSet
-- name    : GlobalTheory.AdLat.det_mem_adelicCompletionOfElementSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:45.629375+00:00
-- url     : https://prove2.me/theorems/200e3e7d-0a79-4aa7-b267-b42ed5a69210
-- title:
--   Ad Lat: det mem adelic Completion Of Element Set
-- statement:
--   The Ad Lat construction uses the det mem adelic Completion Of Element Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L29-L39

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

theorem GlobalTheory.AdLat.det_mem_adelicCompletionOfElementSet {n : ℕ} (r s : Fin n → FractionalIdeal (𝓞 E)⁰ E)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((r i * s j : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    M.det ∈ hat1 F (((∏ i, r i) * ∏ j, s j : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by sorry
