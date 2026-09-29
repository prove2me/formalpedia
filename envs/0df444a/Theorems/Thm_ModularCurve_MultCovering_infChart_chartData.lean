-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_chartData
-- name    : ModularCurve.MultCovering.infChart_chartData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/3a796003-15dd-5b96-a8c0-721a74987518
-- title:
--   Uniform p^B-window making a finite family units of the ∞̄-chart
-- statement:
--   Let $\iota$ be a finite type, let $p$ be a natural number assumed prime, and let $t : \iota \to \overline{F}_{1\cdot p}$ be a family of elements of $\overline{F}_{1\cdot p} =$ `modularFunctionFieldBar (1 * p)`, the subfield of $\overline{\mathbb Q}$-Laurent series generated over $\overline{\mathbb Q}$ by the coefficientwise image of the full modular function field of level $1\cdot p$, and assume $t_l \neq 0$ for every $l$. The assertion is that there is a single exponent $B \in \mathbb N$, depending only on $p$ and the family $t$, such that the following holds for every valuation subring $A \subseteq \overline{\mathbb Q}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $A$, with decidable equality and characteristic $p$ on the residue field of $A$, and for every chart context $\Gamma$ of type `ChartCtx p A` (a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the two Hecke operators $\bar\alpha,\bar\beta$ at level $1$ and prime $p$, a place specialisation $P$ of $A$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{F}_{1\cdot p}$, a finset $W_n$ of places of the characteristic-$p$ function field `modularFunctionFieldC (ResidueField A) 1` which is exactly the set of supersingular places, finiteness of the supersingular $j$-set together with the equality of its cardinality with `mAnnuli p`, and a `ChartFstSupply` datum for $R$ and $S_1$): for each $l \in \iota$ there exists $c \in \overline{\mathbb Q}$ with $c \neq 0$, $p^B c \in A$ and $p^B c^{-1} \in A$, such that $c \cdot t_l$ lies in the valuation subring `(infChart Γ).integers` of $\overline{F}_{1\cdot p}$ and its image under the residue homomorphism `(infChart Γ).residue` into `modularFunctionFieldC (ResidueField A) 1` is nonzero.
--
--   This is the Gauss-prolongation (uniform window) statement for the component chart at $\bar\infty$ attached to a chart context: after rescaling by a constant lying in a window of width controlled by $p^B$, uniformly in the valuation ring $A$ and in the chart context, every member of a prescribed finite family of nonzero modular functions of level $p$ becomes a unit of that chart, i.e. has nonzero reduction. It feeds the construction of a multiplicative covering with a certified family of functions, via [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_chartData.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_chartData {ι : Type} [Fintype ι] (p : ℕ) [Fact p.Prime]
    (t : ι → ↥(modularFunctionFieldBar (1 * p))) (ht : ∀ l, t l ≠ 0) :
    ∃ B : ℕ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      ∀ l : ι, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
        ∃ h : c • t l ∈ (infChart Γ).integers, (infChart Γ).residue ⟨c • t l, h⟩ ≠ 0 := by sorry
