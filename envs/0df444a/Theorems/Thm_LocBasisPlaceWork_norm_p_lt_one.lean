-- Prove2me | Theorems.Thm_LocBasisPlaceWork_norm_p_lt_one
-- name    : LocBasisPlaceWork.norm_p_lt_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:51.556363+00:00
-- url     : https://prove2.me/theorems/f7d2d32a-2bd2-4af7-9346-6fb273fc7d5f
-- title:
--   Loc Basis Place Work: norm p lt one
-- statement:
--   The Loc Basis Place Work construction uses the norm p lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L51-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open LocBasisPlaceWork
variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p])

theorem LocBasisPlaceWork.norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by sorry
