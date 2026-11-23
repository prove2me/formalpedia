-- Prove2me | Theorems.Thm_GlobalTheory_ordTop_vw_of_ne_zero
-- name    : GlobalTheory.ordTop_vw_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:46.408712+00:00
-- url     : https://prove2.me/theorems/debd2bf9-7412-4762-a58e-f8043e97f325
-- title:
--   Global Theory: ord Top vw of ne zero
-- statement:
--   The Global Theory construction uses the ord Top vw of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L235-L236

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

theorem GlobalTheory.ordTop_vw_of_ne_zero {f : F} (hf : f ≠ 0) :
    ordTop_vw V f = (WithZero.log (Ring.ordFrac V f) : ℤ) := by sorry
