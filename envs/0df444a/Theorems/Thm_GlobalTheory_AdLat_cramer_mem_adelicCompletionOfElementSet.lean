-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_cramer_mem_adelicCompletionOfElementSet
-- name    : GlobalTheory.AdLat.cramer_mem_adelicCompletionOfElementSet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:19.477255+00:00
-- url     : https://prove2.me/theorems/f87341a4-40e3-4bff-82ac-6dd6dcb1a2fc
-- title:
--   Ad Lat: cramer mem adelic Completion Of Element Set
-- statement:
--   The Ad Lat construction uses the cramer mem adelic Completion Of Element Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L41-L59

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

theorem GlobalTheory.AdLat.cramer_mem_adelicCompletionOfElementSet {n : ℕ} (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
    (w : Fin n → RA F E) (hw : ∀ i, w i ∈ hat1 F (cI i : Set E)) (a : Fin n) :
    M.cramer w a ∈ hat1 F (cI a : Set E) := by sorry
