-- Prove2me | Theorems.Thm_NoetherianScheme_ringOfIntegers_cyclotomic_infinite
-- name    : NoetherianScheme.ringOfIntegers_cyclotomic_infinite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T22:42:24.052362+00:00
-- url     : https://prove2.me/theorems/bb5735c9-6203-4eab-b9d6-218a3e4e072c
-- title:
--   Ring of integers of ℚ(μ∞): non-Noetherian of dimension 1
-- statement:
--   Let $K = \mathbb Q(\mu_\infty)$ be the field obtained from $\mathbb Q$ by adjoining all roots of unity (precisely: $K$ is generated over $\mathbb Q$ by roots of unity and contains a primitive $n$-th root of unity for every $n \ge 1$). Let $\mathcal O_K$ be the integral closure of $\mathbb Z$ in $K$. Then
--
--   1. $\mathcal O_K$ is **not** a Noetherian ring, and
--   2. $\mathcal O_K$ has Krull dimension exactly $1$.
--
--   So finite-dimensional affine schemes need not be Noetherian.
--
--   **Formalization Note** The source speaks of a general infinite Galois extension "such as" $\mathbb Q(\mu_\infty)/\mathbb Q$; only this explicit example is formalized, since the claim is not true for every infinite algebraic extension.
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), section "Non-examples / Rings of integers over infinite extensions": "Given an infinite Galois field extension L/K, such as Q(ζ_∞)/Q (by adjoining all roots of unity), the ring of integers O_L is a non-Noetherian ring which is dimension 1."

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace NoetherianScheme

theorem ringOfIntegers_cyclotomic_infinite (K : Type u) [Field K] [CharZero K]
    [IsCyclotomicExtension {n : ℕ | 0 < n} ℚ K] :
    ¬ IsNoetherianRing (𝓞 K) ∧ ringKrullDim (𝓞 K) = 1 := by sorry

end NoetherianScheme
