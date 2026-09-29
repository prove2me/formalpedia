-- Prove2me | Theorems.Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
-- name    : ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/3011c392-0465-5c9b-a225-010afb2e33ba
-- title:
--   Bounded denominators with attained Gauss norm at ∞̄
-- statement:
--   Fix $N \ge 1$ and $n \in \mathbb{N}$, and work in the field $F =$ `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\overline{\mathbb{Q}}(\!(q)\!)$ over $\overline{\mathbb{Q}}$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the elements of `modularFunctionFieldFull N` (itself the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the divisor expansions attached to $N$). Let $f \in F$ be nonzero and lie in the Riemann–Roch space of the divisor $n \cdot \bar\infty$, where $\bar\infty$ is the place `cuspInftyBar N` of $F$ over $\overline{\mathbb{Q}}$ given by the $q$-adic valuation subring; explicitly, the adic valuation of $f$ at $\bar\infty$ is at most $\exp(n)$ and at every other place of $F$ over $\overline{\mathbb{Q}}$ at most $\exp(0) = 1$, so $f$ has no pole outside $\bar\infty$ and a pole of order at most $n$ there. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ and $p$ a prime with $p \in A.\mathrm{nonunits}$, i.e. $p$ lies in the maximal ideal of $A$. The conclusion is that there exists $c \in \overline{\mathbb{Q}}$, $c \neq 0$, such that every Laurent coefficient $(c f)_k$, $k \in \mathbb{Z}$, of $c f$ viewed in $\overline{\mathbb{Q}}(\!(q)\!)$ lies in $A$, and at least one coefficient $(c f)_{k_0}$ lies outside the maximal ideal of $A$, hence is a unit of $A$.
--
--   This is the bounded-denominators statement for functions on $X_0(N)$ with poles only at the cusp $\bar\infty$, in the form: the Gauss norm $\sup_k |(f)_k|_A$ of the $q$-expansion is finite and attained, so after scaling by a single nonzero constant the expansion has coefficients in $A$ and is primitive. It supplies the normalisation step for the results on integrality of $q$-expansions and on the Fricke involution, among them [`ModularCurve.exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg`](thm.html#ModularCurve.exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg), [`ModularCurve.exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar`](thm.html#ModularCurve.exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar) and [`ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
    (N : ℕ) [NeZero N] (n : ℕ) (f : modularFunctionFieldBar N)
    (hf : f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) 1)) (hf0 : f ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      (∀ k : ℤ, ((c • f : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) ∧
      ∃ k : ℤ, ((c • f : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits := by sorry
