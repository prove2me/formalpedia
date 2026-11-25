-- Prove2me | Theorems.Thm_GlobalTheory_exists_conductor_adicCompletion_of_essFiniteType
-- name    : GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:06.43629+00:00
-- url     : https://prove2.me/theorems/08e73520-5e3a-432e-a40b-2f5ec35a415f
-- title:
--   Global Theory: exists conductor adic Completion of ess Finite Type
-- statement:
--   The Global Theory construction uses the exists conductor adic Completion of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsConductorAdicCompletionEssFiniteType.lean#L88-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsConductorAdicCompletionEssFiniteType.lean#L88-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsConductorAdicCompletionEssFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by sorry
