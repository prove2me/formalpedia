-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuotientNormSquareData_RowData_glued_fg
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.glued_fg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:54.272923+00:00
-- url     : https://prove2.me/theorems/33b20958-6acb-4aa2-87d3-295f5f7a3dc9
-- title:
--   Row Data: glued fg
-- statement:
--   The Row Data construction uses the glued fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L102-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean#L102-L114

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.glued_fg [Finite T] : D.glued.FG := by sorry
