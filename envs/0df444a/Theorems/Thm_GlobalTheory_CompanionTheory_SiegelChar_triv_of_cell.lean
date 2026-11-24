-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_triv_of_cell
-- name    : GlobalTheory.CompanionTheory.SiegelChar.triv_of_cell
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:41.076774+00:00
-- url     : https://prove2.me/theorems/2bdd93a6-604c-4e47-aa7c-172e2a33b50f
-- title:
--   Siegel Char: triv of cell
-- statement:
--   The Siegel Char construction uses the triv of cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L263-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L263-L437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar

theorem GlobalTheory.CompanionTheory.SiegelChar.triv_of_cell {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by sorry
