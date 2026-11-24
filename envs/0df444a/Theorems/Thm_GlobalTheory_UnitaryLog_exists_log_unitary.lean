-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLog_exists_log_unitary
-- name    : GlobalTheory.UnitaryLog.exists_log_unitary
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:24.606315+00:00
-- url     : https://prove2.me/theorems/22d74bb0-bae8-458a-ab62-06f1684b5124
-- title:
--   Unitary Log: exists log unitary
-- statement:
--   The Unitary Log construction uses the exists log unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L77-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L77-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem GlobalTheory.UnitaryLog.exists_log_unitary (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ →
      (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧
        NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by sorry
