-- Prove2me | Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
-- name    : GlobalTheory.fracKaehlerBasis_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:38.632604+00:00
-- url     : https://prove2.me/theorems/122035d1-ab60-43fa-a59e-caccf5913d65
-- title:
--   Global Theory: frac Kaehler Basis apply
-- statement:
--   The Global Theory construction uses the frac Kaehler Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L294-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L294-L296

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
omit [IsDomain V] [IsDiscreteValuationRing V]

theorem GlobalTheory.fracKaehlerBasis_apply (b : Basis (Fin n) V Ω[V⁄K]) (k : Fin n) :
    fracKaehlerBasis F b k = KaehlerDifferential.map K K V F (b k) := by sorry
