-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Rat_prime_dvd_discr_dvd_conductor
-- name    : IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T16:33:22.141817+00:00
-- url     : https://prove2.me/theorems/f5057246-6fea-4212-94ec-ea78f29cc47c
-- title:
--   Prime divisors of a cyclotomic discriminant divide its conductor
-- statement:
--   If $K/\mathbf Q$ is an $n$-th cyclotomic field and a rational prime $\ell$ divides $\operatorname{disc}(K)$, then $\ell$ divides $n$.
-- source:
--   The explicit cyclotomic discriminant formula `IsCyclotomicExtension.Rat.discr` in Mathlib.

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

set_option autoImplicit false
noncomputable section

/-- Every rational prime dividing the discriminant of an `n`-th cyclotomic
field divides `n`. -/
theorem IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    {l : ℕ} (hl : l.Prime)
    (hldisc : (l : ℤ) ∣ NumberField.discr K) : l ∣ n := by sorry
