-- Prove2me | Theorems.Thm_Ideal_height_map_quotient_eq_one_of_minimalPrimes
-- name    : Ideal.height_map_quotient_eq_one_of_minimalPrimes
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T00:56:54.930451+00:00
-- url     : https://prove2.me/theorems/e6f35e04-db26-40b8-8787-d0750cfc2c4d
-- title:
--   Principal-cut components have relative height one
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $p$ be a prime ideal, and let $x\notin p$. If $q$ is minimal over $p+(x)$, then the image of $q$ in $R/p$ has height exactly one:
--   $$\operatorname{ht}_{R/p}(q/p)=1.$$
--   No homogeneity, field, or equidimensionality hypothesis is required. This is the local codimension part of the hypersurface-component dimension argument; it does not itself identify global quotient dimensions.
-- source:
--   Krull principal ideal theorem, Stacks Project, Section 10.60 (Dimension), https://stacks.math.columbia.edu/tag/00KD; its application to the domain R/p. Supporting algebra for Philippon (1986), Proposition 3.3, printed p. 368.

import Mathlib
set_option autoImplicit false

theorem Ideal.height_map_quotient_eq_one_of_minimalPrimes
{R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (x : R) (hx : x ∉ p)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    (q.map (Ideal.Quotient.mk p)).height = 1 := by sorry
