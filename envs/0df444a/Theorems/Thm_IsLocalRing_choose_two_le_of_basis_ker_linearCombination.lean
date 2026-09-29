-- Prove2me | Theorems.Thm_IsLocalRing_choose_two_le_of_basis_ker_linearCombination
-- name    : IsLocalRing.choose_two_le_of_basis_ker_linearCombination
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/6d4d790a-beb2-5981-a3ff-c0fdaa05d5fa
-- title:
--   Koszul relations force binom m2 generators of the relation module
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, let $m$ be a natural number and let $\sigma : \mathrm{Fin}\,m \to R$ be a family of elements of $R$ which is minimal in the following sense: for every $c : \mathrm{Fin}\,m \to R$, if $\sum_i c_i \sigma_i \in \mathfrak m^2$ then $c_i \in \mathfrak m$ for all $i$. Let $\rho$ be a natural number and suppose the relation module $\ker(\sigma\text{-linear combination map}) = \{c \in R^m : \sum_i c_i\sigma_i = 0\}$, i.e. the kernel of `Fintype.linearCombination R σ` as an $R$-submodule of $\mathrm{Fin}\,m \to R$, admits an $R$-basis $\eta$ indexed by $\mathrm{Fin}\,\rho$. Then $\binom m2 \le \rho$. In particular a free relation module of rank $\rho$ among $m$ minimal elements cannot have rank smaller than $\binom m2$; no hypothesis that $\sigma_i \in \mathfrak m$ is imposed, it being a consequence of the minimality hypothesis applied to $0 \in \mathfrak m^2$.
--
--   This is the elementary lower bound on second Betti numbers coming from Koszul relations: if $m$ elements of a local ring are minimal modulo $\mathfrak m^2$ and their relation module is free, its rank is at least $\binom m2$. It is used in the proof that a local ring presented by a power series basis admits a minimal generating set of its maximal ideal of cardinality at most two, namely by [`IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries`](thm.html#IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_choose_two_le_of_basis_ker_linearCombination.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem IsLocalRing.choose_two_le_of_basis_ker_linearCombination
    {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (σ : Fin m → R)
    (hσ : ∀ c : Fin m → R, ∑ i, c i * σ i ∈ IsLocalRing.maximalIdeal R ^ 2 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    {ρ : ℕ} (η : Module.Basis (Fin ρ) R (LinearMap.ker (Fintype.linearCombination R σ))) :
    m.choose 2 ≤ ρ := by sorry
