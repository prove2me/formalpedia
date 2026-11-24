-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletion_fractionalIdeal_iff
-- name    : GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:43.310937+00:00
-- url     : https://prove2.me/theorems/b02e17a1-3af2-46fd-8663-ca5b4e007fc8
-- title:
--   Ad Lat: one tmul mem adelic Completion fractional Ideal iff
-- statement:
--   The Ad Lat construction uses the one tmul mem adelic Completion fractional Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L114-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L114-L134

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
variable [NumberField E]

theorem GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by sorry
