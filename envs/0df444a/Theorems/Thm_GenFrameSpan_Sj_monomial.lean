-- Prove2me | Theorems.Thm_GenFrameSpan_Sj_monomial
-- name    : GenFrameSpan.Sj_monomial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:50:53.409141+00:00
-- url     : https://prove2.me/theorems/9a52ed3b-ae12-46fc-8d5f-4e701033bba5
-- title:
--   Gen Frame Span: Sj monomial
-- statement:
--   The Gen Frame Span construction uses the Sj monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L42-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]

theorem GenFrameSpan.Sj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (β : Lt × Fin N0 × Fin N1 →₀ ℕ) (c : ℤ) :
    Sj Th (monomial β c) = c • ((β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th) := by sorry
