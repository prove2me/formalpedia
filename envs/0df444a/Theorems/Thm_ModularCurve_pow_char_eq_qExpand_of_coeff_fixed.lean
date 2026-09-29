-- Prove2me | Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
-- name    : ModularCurve.pow_char_eq_qExpand_of_coeff_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/1c575533-584c-5e74-9c93-91a8404f9429
-- title:
--   Frobenius-fixed coefficients: s(q)ᵖ = s(qᵖ)
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime number such that $R$ has characteristic $p$. Let $s$ be a formal Laurent series over $R$, that is, an element of `LaurentSeries R` $=$ `HahnSeries ℤ R`, so $s$ is given by its coefficients $s.\mathrm{coeff}\,k \in R$ indexed by $k \in \mathbb{Z}$ (with well-ordered support). Assume that every coefficient of $s$ is fixed by the $p$-power map: $(s.\mathrm{coeff}\,k)^p = s.\mathrm{coeff}\,k$ for all $k \in \mathbb{Z}$. Then the $p$-th power $s^p$, taken in the ring of Laurent series, equals the image of $s$ under `qExpand R p`, the ring homomorphism on `LaurentSeries R` obtained by re-indexing the support along the injective, order-preserving additive map $k \mapsto p\,k$ of $\mathbb{Z}$; concretely, `qExpand R p s` has coefficient $s.\mathrm{coeff}\,k$ in degree $pk$ and coefficient $0$ in degrees not divisible by $p$. In the usual notation $s = \sum_k a_k q^k$ with $a_k^p = a_k$, the assertion is the identity $s(q)^p = s(q^p)$.
--
--   This is the Frobenius identity on $q$-expansions in characteristic $p$: raising a Laurent series with Frobenius-fixed (e.g. $\mathbb{F}_p$-rational) coefficients to the $p$-th power amounts to substituting $q^p$ for $q$. It underlies the Kronecker-type congruences for modular polynomials and is used in the project's computations with $q$-expansions of modular units and of the $j$-function at level structures, for instance in the analysis of Atkin–Lehner operators on valuation subrings and in producing integral Laurent-series identities for powers of $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.pow_char_eq_qExpand_of_coeff_fixed {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : LaurentSeries R) (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s := by sorry
