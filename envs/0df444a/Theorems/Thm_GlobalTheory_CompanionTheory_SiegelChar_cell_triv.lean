-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_cell_triv
-- name    : GlobalTheory.CompanionTheory.SiegelChar.cell_triv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:50.01938+00:00
-- url     : https://prove2.me/theorems/ddb4fdc8-e020-402b-87ce-1408a19c330e
-- title:
--   Siegel Char: cell triv
-- statement:
--   The Siegel Char construction uses the cell triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L114-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L114-L209

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
variable {E : Type} [CommRing E] {R : Type} [Ring R] [Algebra E R] {c : E → E} {σ : R →+ R}
  {G : Type} [Group G] {φ : G →* R} {e f : R}

theorem GlobalTheory.CompanionTheory.SiegelChar.cell_triv (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1) (hu : ∀ g, σ (φ g) * φ g = 1)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ)
    (hlow : ∀ s, e * s = 0 → s * f = 0 → σ s = -s → ∃ n, φ n = 1 + s ∧ lam n = 1)
    (hP : ∀ g, f * φ g * e = 0 → lam g = 1) (g : G) (hg : IsUnit (φ g * e + f)) : lam g = 1 := by sorry
