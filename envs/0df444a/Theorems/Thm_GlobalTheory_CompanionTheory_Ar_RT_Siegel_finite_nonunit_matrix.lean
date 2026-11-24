-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_finite_nonunit_matrix
-- name    : GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit_matrix
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:20:55.58195+00:00
-- url     : https://prove2.me/theorems/cf848b02-0df0-468d-ac0e-a2abcd2556c4
-- title:
--   Siegel: finite nonunit matrix
-- statement:
--   The Siegel construction uses the finite nonunit matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L28-L41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit_matrix

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

theorem GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit_matrix {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by sorry
