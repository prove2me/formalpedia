-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_char_trivial_artinian
-- name    : GlobalTheory.CompanionTheory.Ar.RT.Siegel.char_trivial_artinian
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:20:34.343662+00:00
-- url     : https://prove2.me/theorems/84ea264f-504a-4093-992b-bc991e9864e7
-- title:
--   Siegel: char trivial artinian
-- statement:
--   The Siegel construction uses the char trivial artinian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L123-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L123-L208

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
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

theorem GlobalTheory.CompanionTheory.Ar.RT.Siegel.char_trivial_artinian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [CommRing E] [IsArtinianRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsUnit ξ → c ξ = -ξ → (∀ x, c (c x) = x) → IsUnit J.det → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by sorry
