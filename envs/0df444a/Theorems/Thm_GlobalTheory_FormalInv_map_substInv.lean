-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_map_substInv
-- name    : GlobalTheory.FormalInv.map_substInv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:22.256255+00:00
-- url     : https://prove2.me/theorems/5ad199b2-2725-43b5-8b81-5feba6af0732
-- title:
--   Formal Inv: map subst Inv
-- statement:
--   The Formal Inv construction uses the map subst Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L474-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L474-L480

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

theorem GlobalTheory.FormalInv.map_substInv {S : Type*} [CommRing S] (φ : R →+* S) (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) :
    (fun i => MvPowerSeries.map φ (substInv u i)) =
      substInv fun i => MvPowerSeries.map φ (u i) := by sorry
