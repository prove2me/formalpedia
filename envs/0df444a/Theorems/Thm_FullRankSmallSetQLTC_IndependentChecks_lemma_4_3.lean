-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_4_3
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:15.100527+00:00
-- url     : https://prove2.me/theorems/75a90203-4b36-4fe8-9efd-21d621199f93
-- title:
--   Lemma 4.3 — non-degeneracy of π_m on non-square norm shells
-- statement:
--   Let $n\equiv1\pmod4$ be a positive integer that is not a perfect square, and let $m\ge3$ satisfy $2^m>2\sqrt n$. Then the reduction $\pi_m$ (reduction modulo $2^m$ followed by the quotient by scalar units, with values in $\widehat G_m$) is injective on $A(n)$, and
--   $$1\notin\pi_m(A(n)).$$
--
--   This is the size argument that keeps the reduced generators distinct and nontrivial.
--
--   Differences from the source:
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: π_m : 1 + 2L(ℤ₂) → Ĝ_m (reduction mod 2^m, then the quotient by scalars), Ĝ_m = U_m/R_m^×, G_m the norm ≡ 1 (mod 8) classes → pim m on integral quaternions (value 1 off the domain a ≡ 1 mod 2); U_m the units of L(ℤ/2^m) reducing to 1 mod 2; G_m the image of the units with norm ≡ 1 (mod 2^min(m,3)); reason: every quaternion the source reduces in this statement is integral and ≡ 1 (mod 2); for m ≥ 3 the groups are those of Definition 4.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 4.3, p. 20 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

/-- **Lemma 4.3** (Non-degeneracy, p. 20). Let `n ≡ 1 (mod 4)` be a positive integer that is not
a square, and let `m ≥ 3` satisfy `2^m > 2√n`. Then `π_m` is injective on `A(n)` and
`1 ∉ π_m(A(n))`. -/
theorem lemma_4_3 (n : ℕ) (hn : 0 < n) (hn4 : n % 4 = 1) (hsq : ¬ IsSquare n) (m : ℕ)
    (hm : 3 ≤ m) (hsep : 2 * Real.sqrt n < 2 ^ m) :
    Set.InjOn (pim m) (APos n) ∧ (1 : GHat m) ∉ Ared m n := by sorry

end FullRankSmallSetQLTC.IndependentChecks
