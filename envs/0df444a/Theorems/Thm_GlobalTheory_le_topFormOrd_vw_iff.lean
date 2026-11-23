-- Prove2me | Theorems.Thm_GlobalTheory_le_topFormOrd_vw_iff
-- name    : GlobalTheory.le_topFormOrd_vw_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:55.065798+00:00
-- url     : https://prove2.me/theorems/021545c6-adfb-4fde-98d3-275616cb8d47
-- title:
--   Global Theory: le top Form Ord vw iff
-- statement:
--   The Global Theory construction uses the le top Form Ord vw iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L359-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L359-L370

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

theorem GlobalTheory.le_topFormOrd_vw_iff {t : V} (ht : Irreducible t) (m : ℤ) (ω : ⋀[F]^n Ω[F⁄K]) :
    (m : WithTop ℤ) ≤ topFormOrd_vw F b ω ↔
      ∃ η ∈ regForms K V F n, ω = algebraMap V F t ^ m • η := by sorry
