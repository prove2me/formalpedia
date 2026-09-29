-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_chartData_goodFamily
-- name    : ModularCurve.MultCovering.infChart_chartData_goodFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/d0fe5243-3171-55fa-9746-bd40b0e0f1c9
-- title:
--   Chart data for the good family on the ∞̄-chart
-- statement:
--   Let $p\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ (i.e. `A.LiesOverPrime p`) and residue field $k$ of characteristic $p$, let $\Gamma$ be a chart context for $p$ and $A$ (modular polynomial data with its Kronecker congruence, integrality of the Hecke $\bar\alpha$ and $\bar\beta$ operators at level $1$, a place specialization with a level-one prolongation pair, a set $S_1$ of places of $\overline{M}(1\cdot p)$, the finset of supersingular places of $M_C(k,1)$, the finiteness of `ssJSet` together with its cardinality $m =$ `mAnnuli p`, and a chart supply), and let $\Phi$ be a family context `FamCtx p r`, with $t =$ `goodFamily` $\Phi : \mathrm{Fin}\,r \to \overline{M}(1\cdot p)$. Write $C =$ `infChart` $\Gamma$. Then every $t_i$ lies in the valuation subring $C.\mathrm{integers}$, and there are maps $c_Q, i_Q$ from places of $M_C(k,1)$ over $k$ to $\mathrm{Fin}\,r$ such that, for all $P$ in $C.\mathrm{dom}$ with reduction $\bar P = C.\mathrm{placeMap}\,P$: both $P$ and $\bar P$ are rational (the structure map onto the residue field is surjective); the $C$-reduction of $t_{c_Q(\bar P)}$ is nonzero; every $t_j t_{c_Q(\bar P)}^{-1}$ lies in $C.\mathrm{integers}$ and in the valuation subring of $P$; the reduction of $t_{i_Q(\bar P)}t_{c_Q(\bar P)}^{-1}$ minus the constant given by its value at $\bar P$ has $\mathrm{ord}_{\bar P}$ equal to $1$; for $P,Q \in C.\mathrm{dom}$ with $\bar P \ne \bar Q$ some $2\times 2$ minor of the matrix of values at $\bar P$ and $\bar Q$ of the reduced quotients is nonzero; and for every real absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$ there is an index $l \ge 1$ with $\mu\bigl(P.\mathrm{evalAt}(t_l t_{c_Q(\bar P)}^{-1})\bigr) = 1$.
--
--   This is the $\bar\infty$-chart instance of the general chart-data criterion [`ModularCurve.exists_chartData_of_lineResidues`](thm.html#ModularCurve.exists_chartData_of_lineResidues), applied to the good family $t$ whose reductions along the chart are $1$ and the products of the supersingular polynomial with a basis of polynomials of degree less than $m$. It supplies the pivot/immersion indices and the integrality, immersion, separation and unit-norm clauses used by [`ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord`](thm.html#ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord), by [`ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom`](thm.html#ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom), and ultimately by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_chartData_goodFamily.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering
open ModularCurve

theorem ModularCurve.MultCovering.infChart_chartData_goodFamily (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r) :
    ∃ (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (infChart Γ).dom, P.IsRational ∧ ((infChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (infChart Γ).dom,
        (infChart Γ).residue ⟨goodFamily Φ (cQ ((infChart Γ).placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ (infChart Γ).integers) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (infChart Γ).dom,
        ∀ hmem : goodFamily Φ (iQ ((infChart Γ).placeMap P))
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers,
        ((infChart Γ).placeMap P).ord ((infChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ Q ∈ (infChart Γ).dom,
        (infChart Γ).placeMap P ≠ (infChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
          (hmQ : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap Q)))⁻¹ ∈ (infChart Γ).integers),
        ∃ i j, ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP i⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP j⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ i⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
          μ (P.evalAt (goodFamily Φ l
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) := by sorry
