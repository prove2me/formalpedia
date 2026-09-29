-- Prove2me | Theorems.Thm_HorizontalPadicL_finiteCorrection_realization_countingTransfer_inverseSeed_v2
-- name    : HorizontalPadicL.finiteCorrection_realization_countingTransfer_inverseSeed_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:50:44.838395+00:00
-- url     : https://prove2.me/theorems/5555d8e3-b40c-4908-9398-a688585504cd
-- title:
--   Faithful realization transfers finite Fourier corrections to twists (inverse-seed convention)
-- statement:
--   Faithful realization and interpolation turn finite Fourier corrections
--   into a bounded-fibre map on primitive Dirichlet characters. Represent the input
--   on its actual conductor support, disjoint from A. A prime-to-p power preserves
--   exact order; correction characters supported on A cannot cancel it.
--   For a fixed output, there are at most phi(p^m) choices of the power and finitely
--   many corrections on A. Conductor growth is bounded by the product of primes
--   indexed by A. This step needs no prime-density assumption.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.finiteCorrection_realization_countingTransfer`.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Faithful realization and interpolation turn finite Fourier corrections
into a bounded-fibre map on primitive Dirichlet characters. Represent the input
on its actual conductor support, disjoint from A. A prime-to-p power preserves
exact order; correction characters supported on A cannot cancel it.
For a fixed output, there are at most phi(p^m) choices of the power and finitely
many corrections on A. Conductor growth is bounded by the product of primes
indexed by A. This step needs no prime-density assumption. -/
theorem finiteCorrection_realization_countingTransfer_inverseSeed_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties)
    {C : Subring ℂ_[p]} (μ : HorizontalMeasure C p L.exponent)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hinterp : ∀ χ,
      μ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (R.realized χ)
        @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
          (k / 2 - 1) ≠ 0)
    (A : Finset ℕ) (hcorr : μ.HasFiniteCorrection m A) :
    Nonempty (CharacterCountingTransfer
      (supportedPrimePowerCharacters L.primeAt A p m)
      (seededPrimePowerTwists ι f η p m B)) := by
  sorry

end HorizontalPadicL
