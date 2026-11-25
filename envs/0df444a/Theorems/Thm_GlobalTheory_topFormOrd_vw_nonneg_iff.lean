-- Prove2me | Theorems.Thm_GlobalTheory_topFormOrd_vw_nonneg_iff
-- name    : GlobalTheory.topFormOrd_vw_nonneg_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:12.703511+00:00
-- url     : https://prove2.me/theorems/d4b0d14b-b38f-40ea-9dda-0f21d434214a
-- title:
--   Global Theory: top Form Ord vw nonneg iff
-- statement:
--   The Global Theory construction uses the top Form Ord vw nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L372-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L372-L375

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

theorem GlobalTheory.topFormOrd_vw_nonneg_iff (ω : ⋀[F]^n Ω[F⁄K]) :
    0 ≤ topFormOrd_vw F b ω ↔ ω ∈ regForms K V F n := by sorry
