-- Prove2me | Theorems.Thm_GlobalTheory_le_ordTop_vw_iff
-- name    : GlobalTheory.le_ordTop_vw_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:41.874995+00:00
-- url     : https://prove2.me/theorems/726d65f3-ce64-438e-b65a-ad2ecb0338f3
-- title:
--   Global Theory: le ord Top vw iff
-- statement:
--   The Global Theory construction uses the le ord Top vw iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L267-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L267-L286

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

theorem GlobalTheory.le_ordTop_vw_iff {t : V} (ht : Irreducible t) (m : ℤ) (f : F) :
    (m : WithTop ℤ) ≤ ordTop_vw V f ↔ ∃ a : V, f = algebraMap V F t ^ m * algebraMap V F a := by sorry
