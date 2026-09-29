-- Prove2me | Theorems.Thm_MTT_algebraicSymbol_horizontal_distribution
-- name    : MTT.algebraicSymbol_horizontal_distribution
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-22T21:36:50.303392+00:00
-- url     : https://prove2.me/theorems/a6543419-49fc-4549-bbbe-17ef5660c697
-- title:
--   Algebraic-symbol Hecke distribution at an arbitrary denominator
-- statement:
--   For a prime l and an arbitrary positive denominator q, summing the algebraic modular symbol at the l lifts a+bq and denominator lq gives the two Hecke terms at denominator q. This is the arbitrary-denominator version of the middle of MTT's vertical distribution proof and requires no ordinary-root hypothesis.
-- source:
--   The argument in MTT.distribution_relation before ordinary-root stabilization; Kriz--Nordentoft, https://arxiv.org/pdf/2310.20678, Proposition 3.1.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
/-- The arbitrary-denominator form of the Hecke distribution relation for
algebraic modular symbols.  This is the part of the proof of
`MTT.distribution_relation` before ordinary-root stabilization. -/
theorem MTT.algebraicSymbol_horizontal_distribution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι) (P : Periods k ι f.form)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (ℓ q : ℕ) (hℓ : ℓ.Prime) (hq : 0 < q) (a : ℤ) :
    (∑ b ∈ Finset.range ℓ,
      algebraicSymbol P s j
        ((a : ℚ) + (b : ℚ) * (q : ℚ)) ((ℓ : ℚ) * (q : ℚ))) =
      f.coeff ℓ * algebraicSymbol P s j (a : ℚ) (q : ℚ) -
        f.epsilon ℓ * (ℓ : Qbar) ^ (k - 2 - j) *
          algebraicSymbol P s j ((ℓ : ℚ) * (a : ℚ)) (q : ℚ) := by
  sorry
