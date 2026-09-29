-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace
-- name    : ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/6baf7c47-622d-5ccb-ad3e-571dde5a7cde
-- title:
--   Uniform p-power window for scaling a finite family in L(n∞̄)
-- statement:
--   Let $N\ge 1$, let $\iota$ be a finite index type, let $n\in\mathbb N$, and let $t:\iota\to$ `modularFunctionFieldBar N` be a family of elements of the function field obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the level-$N$ modular function field inside the Laurent series over $\overline{\mathbb Q}$. Assume each $t_l$ lies in `riemannRochSpace` of the divisor $n\cdot\overline\infty$, i.e. for every place $v$ of this field over $\overline{\mathbb Q}$ the adic valuation of $t_l$ at $v$ is at most $\exp$ of the coefficient of $v$ in the divisor that takes the value $n$ at the $q$-adic place `cuspInftyBar N` and $0$ elsewhere, and assume each $t_l\ne 0$; let $p$ be a prime. Then there is an exponent $B\in\mathbb N$ with the following property. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, let $\bar F$ be a field that is an algebra over the residue field of $A$, and let $C$ be a component chart for $A$ on the function field with values in $\bar F$ (the data of a valuation subring `C.integers`, a surjective residue homomorphism `C.residue` onto $\bar F$ with kernel the maximal ideal, a domain of places, a finite set of nodes and a place map, subject to the axioms of `ComponentChart`). Suppose $C$ satisfies the $q$-coefficient criterion: every $f$ in the same Riemann–Roch space $L(n\cdot\overline\infty)$ all of whose Laurent coefficients lie in $A$ and at least one of whose coefficients is a unit of $A$ lies in `C.integers` and has nonzero residue. Then for every $l\in\iota$ there is $c\in\overline{\mathbb Q}$, $c\ne 0$, with $p^{B}c\in A$ and $p^{B}c^{-1}\in A$, such that $c\cdot t_l$ lies in `C.integers` and has nonzero residue under `C.residue`.
--
--   This provides a scaling factor, confined to a window of $p$-adic size controlled by a single exponent $B$ independent of the valuation subring $A$ above $p$ and of the chart, making each member of a prescribed finite family of nonzero functions with poles only at the cusp $\overline\infty$ (of order at most $n$) a chart integer with nonzero reduction. It is the arbitrary-family form of the window estimate and is cited by [`ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero); the uniformity comes from the fact that the coefficients of each $t_l$ generate a fixed number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace
    (N : ℕ) [NeZero N] {ι : Type} [Fintype ι] (n : ℕ) (t : ι → modularFunctionFieldBar N)
    (ht : ∀ l, t l ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ))) (ht0 : ∀ l, t l ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ (Fbar : Type) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar),
      (∀ f : modularFunctionFieldBar N, f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) →
        (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
        ∃ h : f ∈ C.integers, C.residue ⟨f, h⟩ ≠ 0) →
    ∀ l : ι, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • t l ∈ C.integers, C.residue ⟨c • t l, h⟩ ≠ 0 := by sorry
