-- Prove2me | Theorems.Thm_HorizontalPadicL_residualKernel_discr_prime_dvd_level_mul_p
-- name    : HorizontalPadicL.residualKernel_discr_prime_dvd_level_mul_p
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T15:02:40.6282+00:00
-- url     : https://prove2.me/theorems/ae669fc9-ed13-4e50-af51-60c68eae9f0d
-- title:
--   Prime divisors of a residual kernel-field discriminant divide Np
-- statement:
--   Let $f$ be an MTT eigenform of positive level $N$ and weight $k\geq 2$, let $p$ be prime, and let $D$ be residual Galois-representation data for $f$ at a chosen $p$-adic embedding. If a rational prime $\ell$ divides the discriminant of the finite Galois kernel field recorded by $D$, then $\ell$ divides $Np$. Equivalently, the kernel field is discriminantly unramified away from the modular level and the residue characteristic.
-- source:
--   The discriminant criterion for unramified rational primes, `NumberField.not_dvd_discr_iff_forall_liesOver`, together with the equality between the order of the inertia group and the ramification index.

import Definitions.Def_KN_EigenformResidualGaloisRepresentationV2
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Every rational prime dividing the discriminant of the kernel field of an
eigenform's residual Galois representation divides the product of the modular
level and the residue characteristic. -/
theorem residualKernel_discr_prime_dvd_level_mul_p
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (D : EigenformResidualGaloisRepresentationData hN hk f ιp) :
    letI : Field D.kernelField := D.kernelField_field
    letI : NumberField D.kernelField := D.kernelField_numberField
    ∀ {l : ℕ}, l.Prime →
      (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p := by sorry

end HorizontalPadicL
