-- Prove2me | Theorems.Thm_GlobalTheory_QFNN_integralClosure_of_fractions
-- name    : GlobalTheory.QFNN.integralClosure_of_fractions
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:48.835187+00:00
-- url     : https://prove2.me/theorems/08e4402d-0b29-4170-9a7e-69fd3de6ba3d
-- title:
--   QFNN: integral Closure of fractions
-- statement:
--   The QFNN construction uses the integral Closure of fractions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialA.lean#L8-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialA.lean#L8-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QFNN

theorem GlobalTheory.QFNN.integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by sorry
