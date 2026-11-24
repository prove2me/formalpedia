-- Prove2me | Theorems.Thm_GlobalTheory_finite_twelve_torsion
-- name    : GlobalTheory.finite_twelve_torsion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:10.692831+00:00
-- url     : https://prove2.me/theorems/11de220f-a160-46b1-a82b-1beeca95454a
-- title:
--   Global Theory: finite twelve torsion
-- statement:
--   The Global Theory construction uses the finite twelve torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L88-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
variable [CharZero F] [DecidableEq F]

theorem GlobalTheory.finite_twelve_torsion : {P : W.toAffine.Point | 12 • P = 0}.Finite := by sorry
