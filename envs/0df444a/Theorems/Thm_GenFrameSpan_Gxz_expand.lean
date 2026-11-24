-- Prove2me | Theorems.Thm_GenFrameSpan_Gxz_expand
-- name    : GenFrameSpan.Gxz_expand
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:06.28081+00:00
-- url     : https://prove2.me/theorems/f0398e97-e2bc-4847-8577-300e18a7522c
-- title:
--   Gen Frame Span: Gxz expand
-- statement:
--   The Gen Frame Span construction uses the Gxz expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L114-L121

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

theorem GenFrameSpan.Gxz_expand (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∑ F : (∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0),
      rename (Sum.inl : _ → XZ Lt N0 N1) (∏ s, ∏ c, Dm s _ (F s c)) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (∏ s, ∏ c, Zm s _ (I s c) (F s c)) := by sorry
