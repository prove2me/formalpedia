-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLog_exp_conj_neg_eq
-- name    : GlobalTheory.UnitaryLog.exp_conj_neg_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:16.418014+00:00
-- url     : https://prove2.me/theorems/07cfb217-8c18-4000-8368-c2c10f3df05f
-- title:
--   Unitary Log: exp conj neg eq
-- statement:
--   The Unitary Log construction uses the exp conj neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L27-L33

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

theorem GlobalTheory.UnitaryLog.exp_conj_neg_eq {n : ℕ} (U : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X u : Matrix (Fin n) (Fin n) ℂ)
    (hX : NormedSpace.exp X = u) (hu : uᴴ * (U : Matrix (Fin n) (Fin n) ℂ) * u = U) :
    NormedSpace.exp (-(((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
      (U : Matrix (Fin n) (Fin n) ℂ))) = u := by sorry
