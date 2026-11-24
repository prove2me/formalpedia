-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_lower_triv
-- name    : GlobalTheory.CompanionTheory.SiegelChar.lower_triv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:46.82098+00:00
-- url     : https://prove2.me/theorems/aec4b151-abb4-4073-92c0-f42af9c7e19a
-- title:
--   Siegel Char: lower triv
-- statement:
--   The Siegel Char construction uses the lower triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L14-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L14-L112

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

theorem GlobalTheory.CompanionTheory.SiegelChar.lower_triv (hsm : ∀ (a : E) (x : R), σ (a • x) = c a • σ x) (h1 : σ 1 = 1)
    {i2 i3 : E} (h2 : 2 * i2 = 1) (h3 : 3 * i3 = 1) (c2 : c 2 = 2) (ci2 : c i2 = i2) (ci3 : c i3 = i3)
    (hinj : Function.Injective φ) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ) (s : R) (hes : e * s = 0) (hsf0 : s * f = 0) (hs : σ s = -s) :
    ∃ n, φ n = 1 + s ∧ lam n = 1 := by sorry
