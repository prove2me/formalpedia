-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_PosDet_half_eq
-- name    : GlobalTheory.RealWeil.PosDet.half_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:55.273807+00:00
-- url     : https://prove2.me/theorems/6988828c-99db-49df-b0c5-dc3ab56d3471
-- title:
--   Pos Det: half eq
-- statement:
--   The Pos Det construction uses the half eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HalfAddSelf.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HalfAddSelf.lean#L44-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.PosDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RealWeil.PosDet.half_eq {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (1 / 2 : ℂ) • (1 + (p - (1 - p)) * h * (p - (1 - p)) * g) =
      (p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)) := by sorry
