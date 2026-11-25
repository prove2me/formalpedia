-- Prove2me | Theorems.Thm_LocBasisPlaceWork_plc_ne_bot
-- name    : LocBasisPlaceWork.plc_ne_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:55.263926+00:00
-- url     : https://prove2.me/theorems/ce7ec485-a20e-448f-a4d5-1ca4c9590571
-- title:
--   Loc Basis Place Work: plc ne bot
-- statement:
--   The Loc Basis Place Work construction uses the plc ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L63-L69

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

theorem LocBasisPlaceWork.plc_ne_bot : plc ρ ≠ ⊥ := by sorry
