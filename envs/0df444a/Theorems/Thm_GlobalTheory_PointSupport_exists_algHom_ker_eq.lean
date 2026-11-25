-- Prove2me | Theorems.Thm_GlobalTheory_PointSupport_exists_algHom_ker_eq
-- name    : GlobalTheory.PointSupport.exists_algHom_ker_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:59.674801+00:00
-- url     : https://prove2.me/theorems/c912cbd5-76ec-404b-adbd-c62cfa33979d
-- title:
--   Point Support: exists alg Hom ker eq
-- statement:
--   The Point Support construction uses the exists alg Hom ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBallQuotientEqSumMulFdeg.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBallQuotientEqSumMulFdeg.lean#L12-L21

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

theorem GlobalTheory.PointSupport.exists_algHom_ker_eq (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by sorry
