-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinPresDescent_ker_fg_of_projective
-- name    : GlobalTheory.CompanionTheory.FinPresDescent.ker_fg_of_projective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:16.409544+00:00
-- url     : https://prove2.me/theorems/4dfda2a2-de58-43d0-8f48-887915867172
-- title:
--   Fin Pres Descent: ker fg of projective
-- statement:
--   The Fin Pres Descent construction uses the ker fg of projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L12-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlat.lean#L12-L125

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

theorem GlobalTheory.CompanionTheory.FinPresDescent.ker_fg_of_projective {P C M : Type*} [CommRing P] [CommRing C] [Algebra P C]
    [AddCommGroup M] [Module P M] [Module C M] [IsScalarTower P C M]
    (hsurj : Function.Surjective (algebraMap P C))
    [Module.FinitePresentation P M] [Module.Projective C M]
    (faith : ∀ c : C, (∀ m : M, c • m = 0) → c = 0) :
    (RingHom.ker (algebraMap P C)).FG := by sorry
