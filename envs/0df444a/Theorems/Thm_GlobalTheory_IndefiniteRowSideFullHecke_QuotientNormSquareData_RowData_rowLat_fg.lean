-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuotientNormSquareData_RowData_rowLat_fg
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.rowLat_fg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:48.082656+00:00
-- url     : https://prove2.me/theorems/6bb63e1b-39ba-4c1e-ae41-4827ce730662
-- title:
--   Row Data: row Lat fg
-- statement:
--   The Row Data construction uses the row Lat fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L95-L100

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
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData
variable {T : Type} {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)]
  {τ ε C : Type} [Fintype ε] [DecidableEq ε] {m : ℕ} (D : RowData L T κ τ ε C m)

theorem GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.rowLat_fg (t : T) : (D.rowLat t).FG := by sorry
