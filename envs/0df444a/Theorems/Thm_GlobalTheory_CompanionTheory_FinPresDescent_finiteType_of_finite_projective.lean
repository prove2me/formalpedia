-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinPresDescent_finiteType_of_finite_projective
-- name    : GlobalTheory.CompanionTheory.FinPresDescent.finiteType_of_finite_projective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:01.122562+00:00
-- url     : https://prove2.me/theorems/2b8ef06f-3455-4164-9104-d672394f4496
-- title:
--   Fin Pres Descent: finite Type of finite projective
-- statement:
--   The Fin Pres Descent construction uses the finite Type of finite projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRetr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinPresDescent

theorem GlobalTheory.CompanionTheory.FinPresDescent.finiteType_of_finite_projective (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [Module.Finite C D] [Module.Projective C D] (hinj : Function.Injective (algebraMap C D))
    [Algebra.FiniteType R D] : Algebra.FiniteType R C := by sorry
