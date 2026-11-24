-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_finite_nonunit
-- name    : GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:20:41.34458+00:00
-- url     : https://prove2.me/theorems/950f4271-a7f4-4e25-afc6-9e2dab73a2a9
-- title:
--   Siegel: finite nonunit
-- statement:
--   The Siegel construction uses the finite nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.Siegel

theorem GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by sorry
