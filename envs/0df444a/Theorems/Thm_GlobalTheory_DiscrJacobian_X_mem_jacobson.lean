-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_X_mem_jacobson
-- name    : GlobalTheory.DiscrJacobian.X_mem_jacobson
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:58.563779+00:00
-- url     : https://prove2.me/theorems/df5c2544-7336-424e-b18e-0e92777fd87b
-- title:
--   Discr Jacobian: X mem jacobson
-- statement:
--   The Discr Jacobian construction uses the X mem jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L276-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L276-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct

theorem GlobalTheory.DiscrJacobian.X_mem_jacobson {R : Type} [CommRing R] {σ : Type} (j : σ) :
    (X j : MvPowerSeries σ R) ∈ (⊥ : Ideal (MvPowerSeries σ R)).jacobson := by sorry
