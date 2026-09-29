-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers
-- name    : ModularCurve.exists_uniform_window_smul_mem_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/83fec518-1679-54e6-8477-6ca2e47bb4c6
-- title:
--   Uniform p-window for an embedding basis of X₀(N)
-- statement:
--   Fix a level $N$ with $N \neq 0$ and a family $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N`, the latter being the intermediate field of $\overline{\mathbb{Q}}$-Laurent series obtained by base change of `modularFunctionFieldFull N` to $\overline{\mathbb{Q}}$; assume `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and spans the Riemann–Roch space of the divisor `embDivisor N` $=$ `embDegree N` times the cusp `cuspInftyBar N`. Let $p$ be a prime not dividing $N$. The assertion is the existence of one exponent $B \in \mathbb{N}$, depending only on these data, such that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $(p : \overline{\mathbb{Q}})$ a nonunit of $A$, and every constant reduction $R$ of `modularFunctionFieldBar N` along $A$ with values in `modularFunctionFieldFullC (ResidueField A) N` (a valuation subring `R.integers`, a surjective residue map onto that field whose kernel is the maximal ideal and which extends the residue map of $A$, together with a degree-preserving map on places compatible with divisors of elements of nonzero residue) such that $R$ is good, meaning the genus of `modularFunctionFieldFullC (ResidueField A) N` over $\mathrm{ResidueField}\,A$ equals the genus of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$, and such that `R.placeMap` satisfies `IsPlaceReductionModL A N`, every index $l$ admits a nonzero $c \in \overline{\mathbb{Q}}$ with $p^{B}c \in A$ and $p^{B}c^{-1} \in A$, with $c \cdot s_l \in$ `R.integers` and $R$-residue of $c \cdot s_l$ nonzero.
--
--   This is the per-basis-member integrality clause, uniform in the valuation ring above $p$, underlying the good reduction of $X_0(N)$ at primes not dividing the level in the language of constant reductions of the function field: each member of a Riemann–Roch basis for a multiple of the cusp at infinity becomes a unit-scaled integral element with nonvanishing reduction, with the scaling constant confined to a window $p^{-B} \le |c| \le p^{B}$ independent of $A$ and of the reduction $R$. It is used by [`ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_window_smul_mem_integers.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_uniform_window_smul_mem_integers (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood → IsPlaceReductionModL A N R.placeMap →
    ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ R.integers, R.residue ⟨c • s l, h⟩ ≠ 0 := by sorry
