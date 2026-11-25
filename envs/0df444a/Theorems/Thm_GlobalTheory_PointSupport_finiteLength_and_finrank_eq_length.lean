-- Prove2me | Theorems.Thm_GlobalTheory_PointSupport_finiteLength_and_finrank_eq_length
-- name    : GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:45.095263+00:00
-- url     : https://prove2.me/theorems/daf4dc4c-914d-4b52-b509-4df11312546d
-- title:
--   Point Support: finite Length and finrank eq length
-- statement:
--   The Point Support construction uses the finite Length and finrank eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBallQuotientEqSumMulFdeg.lean#L26-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBallQuotientEqSumMulFdeg.lean#L26-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBallQuotientEqSumMulFdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.PointSupport
open TensorProduct
open TensorProduct

theorem GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by sorry
