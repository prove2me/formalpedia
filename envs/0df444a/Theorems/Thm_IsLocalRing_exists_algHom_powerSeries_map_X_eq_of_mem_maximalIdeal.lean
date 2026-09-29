-- Prove2me | Theorems.Thm_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
-- name    : IsLocalRing.exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c5aaa57a-9f0c-5e0f-8410-099d73bbcc1b
-- title:
--   Evaluation of power series at an element of the maximal ideal
-- statement:
--   Let $\mathcal{O}$ and $R$ be commutative rings in a common universe, with $R$ local, complete and separated for the adic filtration by powers of its maximal ideal $\mathfrak{m}_R$ (in the sense of Mathlib's `IsAdicComplete (maximalIdeal R) R`), and let $R$ be an $\mathcal{O}$-algebra. Let $t \in R$ with $t \in \mathfrak{m}_R$. Then there exists a homomorphism of $\mathcal{O}$-algebras $\mathrm{ev} : \mathcal{O}\llbracket X\rrbracket \to R$ from the ring of one-variable formal power series over $\mathcal{O}$ to $R$ such that: first, $\mathrm{ev}(X) = t$; second, $\mathrm{ev}$ restricted to polynomials is ordinary polynomial evaluation, i.e. for every $p \in \mathcal{O}[X]$ one has $\mathrm{ev}(p) = p(t)$, where $p$ is viewed inside $\mathcal{O}\llbracket X\rrbracket$ by the canonical coercion and $p(t)$ is `Polynomial.aeval t p`; and third, $\mathrm{ev}$ respects the $X$-adic and $\mathfrak{m}_R$-adic filtrations in the sense that for every natural number $n$ and every $F \in \mathcal{O}\llbracket X\rrbracket$ divisible by $X^n$ one has $\mathrm{ev}(F) \in \mathfrak{m}_R^n$. No continuity or uniqueness assertion is made about $\mathrm{ev}$.
--
--   This is the standard universal property of the formal power series ring over $\mathcal{O}$ as an $\mathcal{O}$-algebra: a power series may be evaluated at any topologically nilpotent element of a complete local $\mathcal{O}$-algebra, here at any element of the maximal ideal. It is used by [`IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two`](thm.html#IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two) to produce the comparison map whose bijectivity identifies such a ring with $\mathcal{O}\llbracket X\rrbracket$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
    {𝒪 R : Type u} [CommRing 𝒪] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra 𝒪 R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    ∃ ev : PowerSeries 𝒪 →ₐ[𝒪] R, ev PowerSeries.X = t ∧
      (∀ p : Polynomial 𝒪, ev (p : PowerSeries 𝒪) = Polynomial.aeval t p) ∧
      (∀ (n : ℕ) (F : PowerSeries 𝒪), PowerSeries.X ^ n ∣ F → ev F ∈ maximalIdeal R ^ n) := by sorry
