-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinPresDescent_finitePresentation_of_finite_projective_faithfullyFlat
-- name    : GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:45.901823+00:00
-- url     : https://prove2.me/theorems/8ba5d758-362c-4fa0-ad1f-68adb908c9c4
-- title:
--   Fin Pres Descent: finite Presentation of finite projective faithfully Flat
-- statement:
--   The Fin Pres Descent construction uses the finite Presentation of finite projective faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L131-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L131-L156

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

open GlobalTheory.CompanionTheory.FinPresDescent

theorem GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat :
    ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D]
      [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D →
      Module.FaithfullyFlat C D → Algebra.FinitePresentation R D →
      Algebra.FinitePresentation R C := by sorry
