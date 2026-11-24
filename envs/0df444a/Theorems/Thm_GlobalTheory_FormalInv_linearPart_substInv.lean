-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_linearPart_substInv
-- name    : GlobalTheory.FormalInv.linearPart_substInv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:35.316876+00:00
-- url     : https://prove2.me/theorems/36ec5cc8-1bc8-4c07-938f-aca8b52e8b20
-- title:
--   Formal Inv: linear Part subst Inv
-- statement:
--   The Formal Inv construction uses the linear Part subst Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L409-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L409-L412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}

theorem GlobalTheory.FormalInv.linearPart_substInv (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u)) :
    linearPart (substInv u) = (linearPart u)⁻¹ := by sorry
