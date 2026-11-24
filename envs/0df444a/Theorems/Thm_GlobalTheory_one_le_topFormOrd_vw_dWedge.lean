-- Prove2me | Theorems.Thm_GlobalTheory_one_le_topFormOrd_vw_dWedge
-- name    : GlobalTheory.one_le_topFormOrd_vw_dWedge
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:17.78636+00:00
-- url     : https://prove2.me/theorems/b85f4739-09d4-4e91-9213-23a506342408
-- title:
--   Global Theory: one le top Form Ord vw d Wedge
-- statement:
--   The Global Theory construction uses the one le top Form Ord vw d Wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L399-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L399-L405

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])

theorem GlobalTheory.one_le_topFormOrd_vw_dWedge (x : Fin n → V) {i j : Fin n} (hij : i ≠ j)
    (hi : x i ∈ maximalIdeal V) (hj : x j ∈ maximalIdeal V) :
    1 ≤ topFormOrd_vw F b (dWedge K fun k => algebraMap V F (x k)) := by sorry
