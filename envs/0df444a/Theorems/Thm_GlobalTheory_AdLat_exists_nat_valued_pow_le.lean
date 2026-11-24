-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_exists_nat_valued_pow_le
-- name    : GlobalTheory.AdLat.exists_nat_valued_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:11:00.422374+00:00
-- url     : https://prove2.me/theorems/fdb26ffb-9129-41b7-9250-68d350facb00
-- title:
--   Ad Lat: exists nat valued pow le
-- statement:
--   The Ad Lat construction uses the exists nat valued pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L30-L35

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

theorem GlobalTheory.AdLat.exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by sorry
