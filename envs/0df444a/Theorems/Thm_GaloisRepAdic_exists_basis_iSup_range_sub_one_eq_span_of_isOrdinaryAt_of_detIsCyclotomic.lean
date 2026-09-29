-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
-- name    : GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0cee057a-0acc-500d-9f2a-c81f88104ed8
-- title:
--   Inertia augmentation equals the ordinary line, acting cyclotomically
-- statement:
--   Let $k$ be a field and $p$ a prime with $p \neq 2$, and let $\rho$ be an element of [`GaloisRepAdic k`](def/GaloisRep_Adic.html#L16), that is: a $k$-module $V$ that is free and finite with $\mathrm{finrank}_k V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_k(V)$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9). Assume `ρ.DetIsCyclotomic p`: the image of $p$ in $k$ lies in the maximal ideal, and for all $n$, all $\sigma$ and all $a \in \mathbb{N}$ such that $\sigma\mu = \mu^a$ for every $\mu$ with $\mu^{p^n} = 1$, one has $\det \rho(\sigma) - a \in (p^n)$. Assume also `ρ.IsOrdinaryAt p`: for every valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a nonunit there is a submodule $L$ of $V$ spanned by the first vector of some basis, stable under the decomposition subgroup, and with $\rho(\sigma)v - v \in L$ for all $v \in V$ and all $\sigma$ in the inertia subgroup (the image of the inertia subgroup inside the full Galois group). Finally let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit in $P$. Then there is a basis $b$ of $V$ indexed by `Fin 2` such that the supremum, over $\sigma$ in the inertia subgroup at $P$, of the ranges of $\rho(\sigma) - \mathrm{id}$ equals the line $k \cdot b_0$, and such that for every inertia element $\sigma$ at $P$ and every $a \in \mathbb{N}$ with $\sigma\mu = \mu^a$ for all $p$-th roots of unity $\mu$, one has $\rho(\sigma)(b_0) = a \cdot b_0$.
--
--   This is the residual statement that, for an odd prime $p$ and a two-dimensional representation over a field which is ordinary at $p$ with cyclotomic determinant, the inertia augmentation submodule $\sum_{\sigma \in I_P}(\rho(\sigma)-1)V$ is exactly the ordinary line, on which inertia acts through the mod $p$ cyclotomic character. It is used in the comparison of flat and ordinary local conditions and in the computation that the trace on inertia coinvariants is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic k) (hdet : ρ.DetIsCyclotomic p) (hord : ρ.IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ b : Module.Basis (Fin 2) k ρ.V,
      (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) = k ∙ b 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → ρ.ρ σ (b 0) = (a : k) • b 0 := by sorry
