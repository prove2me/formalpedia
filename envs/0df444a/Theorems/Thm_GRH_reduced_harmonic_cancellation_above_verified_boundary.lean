-- Prove2me | Theorems.Thm_GRH_reduced_harmonic_cancellation_above_verified_boundary
-- name    : GRH.reduced_harmonic_cancellation_above_verified_boundary
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:18:29.859178+00:00
-- url     : https://prove2.me/theorems/26e6bf8c-25d2-4f73-8f2d-6778696adf57
-- title:
--   Simultaneous coprime harmonic Möbius and Liouville cancellation above 0.8749570698
-- statement:
--   For every fixed positive modulus q and every exponent 0.8749570698 < σ < 1, both coprime harmonic sums over 1≤n≤U, weighted by μ(n)/n and by λ(n)/n respectively, have absolute value at most K(q,σ)(U+1)^(σ−1), for all U. The numerical range uses the verified uniform Dirichlet zero-free boundary available in the campaign.
-- source:
--   This gives the proved exponent range of harmonic frontier 005c4a44 and its Möbius counterpart, using the imported LW56e2 bound via 956d623a. The Abel-summation argument adapts the public proof for 17c42452 to a single strictly intermediate fixed exponent. The square-divisor and coprime transfers are d51775f3, ca0f885d, 3567dbaa and ae1711f2.

import Definitions.Def_GRH_MoebiusBilinear

set_option autoImplicit false

namespace GRH

theorem reduced_harmonic_cancellation_above_verified_boundary (q : ℕ) [NeZero q] (σ : ℝ)
    (hσ : 0.8749570698 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      max |reducedLiouvilleHarmonic q U| |reducedMoebiusHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by sorry

end GRH
