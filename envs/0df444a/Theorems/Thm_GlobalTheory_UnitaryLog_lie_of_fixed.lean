-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLog_lie_of_fixed
-- name    : GlobalTheory.UnitaryLog.lie_of_fixed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:03.239095+00:00
-- url     : https://prove2.me/theorems/99365026-f00c-51f0-9027-c51426a42df7
-- title:
--   Unitary Log: lie of fixed
-- statement:
--   The Unitary Log construction uses the lie of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L35-L42

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

theorem GlobalTheory.UnitaryLog.lie_of_fixed {n : ℕ} (U : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : X = -(((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
      (U : Matrix (Fin n) (Fin n) ℂ))) : Xᴴ * (U : Matrix (Fin n) (Fin n) ℂ) + (U : Matrix (Fin n) (Fin n) ℂ) * X = 0 := by sorry
