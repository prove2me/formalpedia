-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_mem_adelicIdeal_one_iff_integral
-- name    : GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:07:14.927797+00:00
-- url     : https://prove2.me/theorems/2902e016-e05f-4947-9f7d-b4c9d6ea69a3
-- title:
--   Ad Lat: mem adelic Ideal one iff integral
-- statement:
--   The Ad Lat construction uses the mem adelic Ideal one iff integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteAdeleStrongApproximationModNat.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteAdeleStrongApproximationModNat.lean#L13-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
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

theorem GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by sorry
