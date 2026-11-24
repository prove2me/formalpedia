-- Prove2me | Theorems.Thm_GenFrameSpan_minorXZ_expand
-- name    : GenFrameSpan.minorXZ_expand
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:50:46.418437+00:00
-- url     : https://prove2.me/theorems/7df94e7b-8b30-4182-afcc-27fbb655f5ac
-- title:
--   Gen Frame Span: minor XZ expand
-- statement:
--   The Gen Frame Span construction uses the minor XZ expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L93-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L93-L112

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

theorem GenFrameSpan.minorXZ_expand (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I = ∑ f : Fin p → Fin N0,
      rename (Sum.inl : _ → XZ Lt N0 N1) (Dm s p f) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (Zm s p I f) := by sorry
