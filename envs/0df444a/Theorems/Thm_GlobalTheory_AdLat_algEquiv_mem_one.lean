-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_algEquiv_mem_one
-- name    : GlobalTheory.AdLat.algEquiv_mem_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:54:06.769322+00:00
-- url     : https://prove2.me/theorems/739f0e57-36a5-40f4-9492-34f0e0a3366c
-- title:
--   Ad Lat: alg Equiv mem one
-- statement:
--   The Ad Lat construction uses the alg Equiv mem one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CramerMemAdelicCompletionOfElementSet.lean#L61-L65

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

theorem GlobalTheory.AdLat.algEquiv_mem_one (c : E ≃ₐ[F] E) (x : E) (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by sorry
