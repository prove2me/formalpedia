-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isTaylorExpansionOn_mvPolynomial
-- name    : FunctorialResolution.EmbeddedResolution.isTaylorExpansionOn_mvPolynomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:49.340894+00:00
-- url     : https://prove2.me/theorems/948a2e6d-0b8c-461c-a014-d1608d819d6c
-- title:
--   Embedded Resolution: is Taylor Expansion On mv Polynomial
-- statement:
--   The Embedded Resolution construction uses the is Taylor Expansion On mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L118-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L118-L152

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing

theorem FunctorialResolution.EmbeddedResolution.isTaylorExpansionOn_mvPolynomial {k : Type*} [CommRing k] {ι : Type*}
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hβ : β ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      φ (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) =
        φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = 0)
    (hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) -
          φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) φ φ' D β := by sorry
