-- Prove2me | Theorems.Thm_GenFrameSpan_prodD_mem
-- name    : GenFrameSpan.prodD_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:16.609063+00:00
-- url     : https://prove2.me/theorems/ee6c0cbc-260a-4b28-af2b-e9c54be22ec1
-- title:
--   Gen Frame Span: prod D mem
-- statement:
--   The Gen Frame Span construction uses the prod D mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L130-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L130-L155

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

theorem GenFrameSpan.prodD_mem (nu : Lt → YoungDiagram)
    (F : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0) :
    map (Int.castRingHom ℂ_[l]) (∏ s, ∏ c, Dm s _ (F s c)) ∈ nablaSpanC Lt l N0 nu := by sorry
