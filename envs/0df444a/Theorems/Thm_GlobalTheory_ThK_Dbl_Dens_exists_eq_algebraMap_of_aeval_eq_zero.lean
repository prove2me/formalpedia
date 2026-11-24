-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_eq_algebraMap_of_aeval_eq_zero
-- name    : GlobalTheory.ThK.Dbl.Dens.exists_eq_algebraMap_of_aeval_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:43.499744+00:00
-- url     : https://prove2.me/theorems/0cd65a8c-e30a-450d-98d3-bafb3aa12cec
-- title:
--   Dens: exists eq algebra Map of aeval eq zero
-- statement:
--   The Dens construction uses the exists eq algebra Map of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L15-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L15-L52

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

theorem GlobalTheory.ThK.Dbl.Dens.exists_eq_algebraMap_of_aeval_eq_zero (φ : Module.End R V) {p : ℂ[X]} (hp : p ≠ 0)
    (hφ : aeval φ p = 0) : ∃ c : ℂ, φ = algebraMap ℂ (Module.End R V) c := by sorry
