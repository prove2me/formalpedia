-- Prove2me | Theorems.Thm_MTT_algebraicSymbol_horizontal_unitFiber_distribution
-- name    : MTT.algebraicSymbol_horizontal_unitFiber_distribution
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-22T21:40:53.42754+00:00
-- url     : https://prove2.me/theorems/bca739d8-579a-4d9d-9051-7b53068fe676
-- title:
--   Central algebraic-symbol distribution over unit lifts
-- statement:
--   At the central exponent 2j=k-2, remove from the arbitrary-denominator distribution relation the unique lift divisible by l. Homogeneity of the algebraic symbol turns that exceptional term into the inverse-residue contribution, giving the three-term coefficientwise horizontal norm relation.
-- source:
--   Kriz--Nordentoft, https://arxiv.org/pdf/2310.20678, Proposition 3.1 and Corollary 3.6; the proof of MTT.distribution_relation.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
/-- Removing the unique lift divisible by `ℓ` from the arbitrary-denominator
symbol distribution relation gives the coefficientwise horizontal norm
relation at the central exponent. -/
theorem MTT.algebraicSymbol_horizontal_unitFiber_distribution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι) (P : Periods k ι f.form)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2) (hcentral : 2 * j = k - 2)
    (ℓ q : ℕ) (hℓ : ℓ.Prime) (hq : 0 < q) (hcop : Nat.Coprime ℓ q)
    (a c b₀ : ℕ) (hb₀ : b₀ < ℓ) (hlift : a + b₀ * q = ℓ * c) :
    (∑ b ∈ (Finset.range ℓ).erase b₀,
      algebraicSymbol P s j
          ((a : ℚ) + (b : ℚ) * (q : ℚ)) ((ℓ : ℚ) * (q : ℚ)) /
        ((ℓ : Qbar) * (q : Qbar)) ^ j) =
      f.coeff ℓ / (ℓ : Qbar) ^ j *
          (algebraicSymbol P s j (a : ℚ) (q : ℚ) / (q : Qbar) ^ j) -
        algebraicSymbol P s j (c : ℚ) (q : ℚ) / (q : Qbar) ^ j -
        f.epsilon ℓ *
          (algebraicSymbol P s j ((ℓ : ℚ) * (a : ℚ)) (q : ℚ) /
            (q : Qbar) ^ j) := by
  sorry
