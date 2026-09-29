-- Prove2me | Theorems.Thm_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
-- name    : IntermediateField.exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ade432e0-d3c5-5303-b897-44c6e4f1a4e0
-- title:
--   Units of K are norms from K(μ_{q^N-1})
-- statement:
--   Let $q$ be a prime and let $K$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ (the algebraic closure `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$. Let $N$ be a natural number with $0 < N$, and let $L$ denote the subfield of $\overline{\mathbb{Q}}_q$ obtained by adjoining to $K$ the set of all $\zeta \in \overline{\mathbb{Q}}_q$ satisfying $\zeta^{q^N-1} = 1$, i.e. the full group of $(q^N-1)$-st roots of unity; $L$ is assumed to be finite-dimensional over $K$. Let $u$ be an element of $K$ whose image in $\overline{\mathbb{Q}}_q$ has absolute value $\lVert u \rVert = 1$ for the canonical extension of the $q$-adic absolute value. The assertion is that there exists $w \in L$ with $\mathrm{N}_{L/K}(w) = u$, the norm being `Algebra.norm K` of the $K$-algebra $L$, so that the equality is an equality of elements of $K$. Nothing is asserted about $w$ beyond its existence; in particular $w$ is not claimed to be a unit.
--
--   This is the surjectivity of the norm map onto the units of $K$ for the unramified layer $K(\mu_{q^N-1})/K$, equivalently the vanishing of the Tate group $\hat H^0(\mathrm{Gal}(L/K), \mathcal{O}_L^\times)$ for this cyclic extension. It is used in the computation of the local invariant attached to the Frobenius cocycle, namely by [`groupCohomology.localInv_apply_eq_valuation_of_carryFun`](thm.html#groupCohomology.localInv_apply_eq_valuation_of_carryFun) and [`groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd`](thm.html#groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IntermediateField

theorem IntermediateField.exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (u : K) (hu : ‖(u : PadicAlgCl q)‖ = 1) :
    ∃ w : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), Algebra.norm K w = u := by sorry
