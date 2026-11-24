-- Prove2me | Theorems.Thm_GenFrameSpan_sfe_inl_inr
-- name    : GenFrameSpan.sfe_inl_inr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:49.733795+00:00
-- url     : https://prove2.me/theorems/24a35ca2-0fba-4355-a7df-f9f3cff04fe3
-- title:
--   Gen Frame Span: sfe inl inr
-- statement:
--   The Gen Frame Span construction uses the sfe inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L58-L65

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

theorem GenFrameSpan.sfe_inl_inr (α : Lt × ℕ × Fin N0 →₀ ℕ) (β : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp
      (α.mapDomain (Sum.inl : _ → XZ Lt N0 N1) + β.mapDomain Sum.inr) = (α, β) := by sorry
