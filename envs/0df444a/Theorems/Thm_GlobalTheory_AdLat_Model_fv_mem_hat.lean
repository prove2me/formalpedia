-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Model_fv_mem_hat
-- name    : GlobalTheory.AdLat.Model.fv_mem_hat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:16.996982+00:00
-- url     : https://prove2.me/theorems/d4ea1958-c091-4780-9ef5-693292d812be
-- title:
--   Model: fv mem hat
-- statement:
--   The Model construction uses the fv mem hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/SmulBasisMemHatIff.lean#L65-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.AdLat.Model.fv_mem_hat {n : ℕ} {L : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) : fv F x ∈ hat F L := by sorry
