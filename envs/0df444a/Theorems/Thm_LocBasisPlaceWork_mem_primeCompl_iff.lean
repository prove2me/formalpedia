-- Prove2me | Theorems.Thm_LocBasisPlaceWork_mem_primeCompl_iff
-- name    : LocBasisPlaceWork.mem_primeCompl_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:55.852048+00:00
-- url     : https://prove2.me/theorems/37555a90-b218-403b-8c57-c5b9c11a67b6
-- title:
--   Loc Basis Place Work: mem prime Compl iff
-- statement:
--   The Loc Basis Place Work construction uses the mem prime Compl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalBasisAtPrime/MemPrimeComplIff.lean#L71-L73

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

theorem LocBasisPlaceWork.mem_primeCompl_iff (s : 𝓞 E) : s ∈ (plc ρ).primeCompl ↔ ‖ρ (s : E)‖ = 1 := by sorry
