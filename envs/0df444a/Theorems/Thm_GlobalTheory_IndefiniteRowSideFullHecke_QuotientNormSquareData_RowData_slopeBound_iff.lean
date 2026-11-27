-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuotientNormSquareData_RowData_slopeBound_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.slopeBound_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:45.0658+00:00
-- url     : https://prove2.me/theorems/d50fb15f-133d-4b90-987f-4c9da2add373
-- title:
--   Row Data: slope Bound iff
-- statement:
--   The Row Data construction uses the slope Bound iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L124-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L124-L144

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
variable {L : Type} [Field L] [NumberField L]

theorem GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.slopeBound_iff [StarRing L] {T : Type} [Finite T] {κ : T → Type} [∀ t, Fintype (κ t)]
    [∀ t, DecidableEq (κ t)] {τ ε C : Type} [Fintype ε] [DecidableEq ε] {m : ℕ}
    (D : RowData L T κ τ ε C m) (h0 : D.glued ≠ ⊥) (hh : ℝ) :
    D.SlopeBound hh ↔ Formalism.HN.muMaxDef (Pi.basisFun L ε) D.XE D.glued ≤ hh - D.logKap := by sorry
