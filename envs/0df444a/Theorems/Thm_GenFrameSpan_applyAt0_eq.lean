-- Prove2me | Theorems.Thm_GenFrameSpan_applyAt0_eq
-- name    : GenFrameSpan.applyAt0_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:50:51.197323+00:00
-- url     : https://prove2.me/theorems/f22ceb2e-4034-42d6-952c-8c165c45bc6f
-- title:
--   Gen Frame Span: apply At0 eq
-- statement:
--   The Gen Frame Span construction uses the apply At0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L50-L56

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

theorem GenFrameSpan.applyAt0_eq (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : applyAt0 N0 N1 l Th P = Lj Th P := by sorry
