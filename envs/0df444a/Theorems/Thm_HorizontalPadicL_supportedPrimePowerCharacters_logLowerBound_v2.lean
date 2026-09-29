-- Prove2me | Theorems.Thm_HorizontalPadicL_supportedPrimePowerCharacters_logLowerBound_v2
-- name    : HorizontalPadicL.supportedPrimePowerCharacters_logLowerBound_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:07:27.089108+00:00
-- url     : https://prove2.me/theorems/0054b663-18b7-4aa9-8466-1835ce747a3d
-- title:
--   Counting exact-order characters on positive-density prime sets
-- statement:
--   Counting exact-order characters supported on a positive-density set of
--   primes congruent to 1 modulo p^m, after finitely many primes are excluded.
--   The strict slack in alpha avoids an endpoint asymptotic from mere natural
--   density. Intended proof: weighted squarefree counting (a weakened form of
--   Kriz--Nordentoft Lemma 5.7), followed by removing lower-order characters.
--   Source: https://arxiv.org/pdf/2310.20678 .
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Counting exact-order characters supported on a positive-density set of
primes congruent to 1 modulo p^m, after finitely many primes are excluded.
The strict slack in alpha avoids an endpoint asymptotic from mere natural
density. Intended proof: weighted squarefree counting (a weakened form of
Kriz--Nordentoft Lemma 5.7), followed by removing lower-order characters.
Source: https://arxiv.org/pdf/2310.20678 . -/
theorem supportedPrimePowerCharacters_logLowerBound_v2
    (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    (ℓ : ℕ → ℕ) (hprime : ∀ n, (ℓ n).Prime)
    (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ)
    (A : Finset ℕ) :
    ∃ α : ℝ, 0 < α ∧ α < ((p ^ m - 1 : ℕ) : ℝ) * δ ∧
      HasLogPowerLowerBound
        (characterConductorCount (supportedPrimePowerCharacters ℓ A p m)) α := by
  sorry

end HorizontalPadicL
