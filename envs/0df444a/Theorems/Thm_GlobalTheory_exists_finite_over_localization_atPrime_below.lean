-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_over_localization_atPrime_below
-- name    : GlobalTheory.exists_finite_over_localization_atPrime_below
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:25.277065+00:00
-- url     : https://prove2.me/theorems/7dbc083a-c1fe-4b66-bf30-01b492e205a7
-- title:
--   Global Theory: exists finite over localization at Prime below
-- statement:
--   The Global Theory construction uses the exists finite over localization at Prime below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsConductorAdicCompletionEssFiniteType.lean#L13-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsConductorAdicCompletionEssFiniteType.lean#L13-L86

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

theorem GlobalTheory.exists_finite_over_localization_atPrime_below (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by sorry
