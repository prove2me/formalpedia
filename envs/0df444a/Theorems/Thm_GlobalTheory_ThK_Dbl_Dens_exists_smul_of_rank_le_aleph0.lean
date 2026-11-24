-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_smul_of_rank_le_aleph0
-- name    : GlobalTheory.ThK.Dbl.Dens.exists_smul_of_rank_le_aleph0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:36.888901+00:00
-- url     : https://prove2.me/theorems/62490291-ed84-4eaf-a96b-06b1a6171f5b
-- title:
--   Dens: exists smul of rank le aleph0
-- statement:
--   The Dens construction uses the exists smul of rank le aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L54-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L54-L107

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]

theorem GlobalTheory.ThK.Dbl.Dens.exists_smul_of_rank_le_aleph0 (hV : Module.rank ℂ V ≤ ℵ₀) (φ : Module.End R V) :
    ∃ c : ℂ, ∀ m, φ m = c • m := by sorry
