-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rational_inv_mul_mem_converseCongruence_gauge3_le
-- name    : LanglandsTunnell.CubicInduction.exists_rational_inv_mul_mem_converseCongruence_gauge3_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/733a574b-19a6-5cdc-8cea-5dad70c73e50
-- title:
--   Rational representatives of polynomially bounded gauge on GL₃(A_ℚ)
-- statement:
--   Let $S$ be a finite set of height-one primes of the ring of integers of $\mathbb{Q}$ and let $a$ assign a natural number $a(v)$ to every such prime. Then there exist a real constant $C$ and a natural number $N$, depending only on $S$ and $a$, such that for every $x \in \mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ there is a matrix $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, embedded adelically through the entrywise structure map, for which the point $y = (\gamma)^{-1} x$ satisfies the following two conditions. First, for every $v \in S$ the $v$-component of $y$ in $\mathrm{GL}_3$ of the completion of $\mathbb{Q}$ at $v$ lies in `converseCongruenceSet3 v (a v)`: both it and its inverse have all entries of valuation at most $1$, its $(0,1)$ and $(2,0)$ entries have valuation at most $\exp(-a(v))$, and its $(2,1)$ entry has valuation at most $\exp(-2a(v))$. Second, $\mathrm{gauge}_3(y) \le C\,\mathrm{gauge}_3(x)^N$, where $\mathrm{gauge}_3$ is the maximum of $1$ and the product of $1 + \sum_w \mathrm{matrixSize}$ of the archimedean components over the infinite places with the finite product over all height-one primes of the sup-sizes of the local components.
--
--   This is the quantitative reduction-theoretic input for $\mathrm{GL}_3$ over $\mathbb{Q}$: every adelic point can be moved by a rational matrix into a prescribed congruence position at finitely many primes, at the cost of a polynomial growth of the gauge. It is used in the construction of the $\mathrm{GL}_3$ automorphy datum, via [`LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe`](thm.html#LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe), where the slowly increasing bound is needed to extend functions from the congruence locus to the whole group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rational_inv_mul_mem_converseCongruence_gauge3_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_rational_inv_mul_mem_converseCongruence_gauge3_le
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ γ : GL (Fin 3) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v ((globalPointsGL 3 (𝓞 ℚ) ℚ γ)⁻¹ * x) ∈ converseCongruenceSet3 v (a v)) ∧
      gauge3 ℚ ((globalPointsGL 3 (𝓞 ℚ) ℚ γ)⁻¹ * x) ≤ C * gauge3 ℚ x ^ N := by sorry
