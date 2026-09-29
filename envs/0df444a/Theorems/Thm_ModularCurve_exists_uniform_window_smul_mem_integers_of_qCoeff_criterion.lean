-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
-- name    : ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/1db71ec0-cc3a-56f6-aebf-5ae956f6d8d1
-- title:
--   Uniform p-power window for model bases at q-criterion charts
-- statement:
--   Let $N\ge 1$, let $r\ge 0$ and let $s\colon \mathrm{Fin}\,r \to \bar F_N$ be a family in the modular function field $\bar F_N =$ `modularFunctionFieldBar N` (the base change to $\bar{\mathbb Q}$ of the full modular function field of level $N$, realised inside $\bar{\mathbb Q}((q))$) which is an `IsEmbBasis`, that is: $s$ is linearly independent over $\bar{\mathbb Q}$ and its range spans the Riemann–Roch space $L(D)$ of the divisor $D = (2g+1)\cdot\bar\infty$, where $g$ is the genus of $\bar F_N$ and $\bar\infty =$ `cuspInftyBar N`; here $L(D)$ is the space of $f$ with $v(f)\le \exp(D(v))$ at every place $v$ of $\bar F_N$ over $\bar{\mathbb Q}$. Let $p$ be a prime. Then there is an exponent $B\in\mathbb N$, depending only on these data, such that for every valuation subring $A\subseteq\bar{\mathbb Q}$ lying over $p$ (meaning $p$ is a non-unit of $A$), every field $\bar{\mathcal F}$ that is an algebra over the residue field of $A$, and every component chart $C$ of $\bar F_N$ along $A$ with values in $\bar{\mathcal F}$ (a valuation subring $C.\mathrm{integers}$ of $\bar F_N$ together with a surjective reduction map onto $\bar{\mathcal F}$ whose kernel is the maximal ideal, a domain of places, a finite set of nodes, a map on places, and the compatibilities recorded in `ComponentChart`), the following holds: if $C$ satisfies the $q$-coefficient criterion — every $f\in L(D)$ all of whose Laurent coefficients lie in $A$ and which has at least one Laurent coefficient that is a unit of $A$ lies in $C.\mathrm{integers}$ and has non-zero residue — then for every index $l$ there is a scalar $c\in\bar{\mathbb Q}$, $c\neq 0$, with $p^{B}c\in A$ and $p^{B}c^{-1}\in A$, such that $c\,s_l$ lies in $C.\mathrm{integers}$ and has non-zero residue in $\bar{\mathcal F}$.
--
--   This is the window clause in the construction of a uniform multiplicative covering of $X_0(N)$: it says that a fixed basis of $L((2g+1)\bar\infty)$ can be rescaled to a chart unit by constants confined to a $p$-power window whose exponent does not depend on the valuation ring above $p$ nor on the chart, the chart being constrained only by the $q$-expansion unit criterion (so no good-reduction hypothesis on $p$ relative to $N$ is made). It is used by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
    (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ (Fbar : Type) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar),
      (∀ f : modularFunctionFieldBar N, f ∈ riemannRochSpace (embDivisor N) →
        (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
        ∃ h : f ∈ C.integers, C.residue ⟨f, h⟩ ≠ 0) →
    ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ C.integers, C.residue ⟨c • s l, h⟩ ≠ 0 := by sorry
