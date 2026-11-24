-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_triv_of_cell
-- name    : GlobalTheory.CompanionTheory.Ar.RT.Siegel.triv_of_cell
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:20:31.735929+00:00
-- url     : https://prove2.me/theorems/ebb8fbab-2a47-461e-9365-baded6e2c651
-- title:
--   Siegel: triv of cell
-- statement:
--   The Siegel construction uses the triv of cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L43-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/FiniteNonunitMatrix.lean#L43-L121

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_triv_of_cell

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

theorem GlobalTheory.CompanionTheory.Ar.RT.Siegel.triv_of_cell {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by sorry
