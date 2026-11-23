-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_right
-- name    : GlobalTheory.RealWeil.PosDet.det_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:15.716806+00:00
-- url     : https://prove2.me/theorems/5ca7afda-ca46-4389-b252-e880cb9b45f0
-- title:
--   Pos Det: det right
-- statement:
--   The Pos Det construction uses the det right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HalfAddSelf.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HalfAddSelf.lean#L20-L27

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

theorem GlobalTheory.RealWeil.PosDet.det_right {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (g * p + (1 - p)).det = (p * g * p + (1 - p)).det := by sorry
