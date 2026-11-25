-- Prove2me | Theorems.Thm_GlobalTheory_topFormOrd_vw_eq_top_iff
-- name    : GlobalTheory.topFormOrd_vw_eq_top_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:08.189388+00:00
-- url     : https://prove2.me/theorems/0351e547-fb98-4282-864b-3fb6b29324eb
-- title:
--   Global Theory: top Form Ord vw eq top iff
-- statement:
--   The Global Theory construction uses the top Form Ord vw eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L354-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L354-L357

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

theorem GlobalTheory.topFormOrd_vw_eq_top_iff (ω : ⋀[F]^n Ω[F⁄K]) : topFormOrd_vw F b ω = ⊤ ↔ ω = 0 := by sorry
