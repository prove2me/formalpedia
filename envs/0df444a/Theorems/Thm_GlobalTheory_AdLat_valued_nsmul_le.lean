-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_valued_nsmul_le
-- name    : GlobalTheory.AdLat.valued_nsmul_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:16.06904+00:00
-- url     : https://prove2.me/theorems/16ce55b9-be88-4ce7-aae3-4232e6e5be70
-- title:
--   Ad Lat: valued nsmul le
-- statement:
--   The Ad Lat construction uses the valued nsmul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L64-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.AdLat.valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by sorry
