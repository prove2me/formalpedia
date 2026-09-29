-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_lt_thirteen
-- name    : ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_lt_thirteen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/71d52d57-7317-51cd-b31f-348b667ae7ce
-- title:
--   Zero-chart data for the rescaled good family, 5≤ p<13
-- statement:
--   Let $p$ be a prime with $5 \le p < 13$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ (the content of `LiesOverPrime`) and residue field $k$ of characteristic $p$, let $\Gamma$ be a chart context for $p$ over $A$ and $\Delta$ an annulus context over $\Gamma$, and let $\Phi$ be a family context `FamCtx p r` for some $r$. Write $t'_l = (p^{\mathrm{hasseExp}\,\Phi\,l})^{-1} t_l$ for the rescaled members `goodFamilyZero Φ.toFamData l`, and let $\mathcal C =$ `zeroChart Γ`, the component chart obtained from the chart at infinity by comap along the Fricke involution on $\overline{\mathcal F}(1\cdot p)$. Assume that all $t'_l$ lie in the valuation subring $\mathcal C$.integers and that their residues in $\mathcal C$, valued in the function field $\mathcal{F}_{\mathbb C}(k,1) =$ `modularFunctionFieldC k 1`, are $k$-linearly independent. Assume also given a nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ with $A = \{\mu \le 1\}$. Then the $t'_l$ are $\mathcal C$-integral and there exist two index functions $c_Q, i_Q$ from the places of $\mathcal{F}_{\mathbb C}(k,1)$ over $k$ to $\mathrm{Fin}\,r$ such that, for every place $P$ in $\mathcal C$.dom: $P$ and its image $\mathcal C.\mathrm{placeMap}(P)$ are rational (the structure map to the residue field is surjective); the $\mathcal C$-residue of the pivot $t'_{c_Q(\mathcal C.\mathrm{placeMap}(P))}$ is nonzero; every ratio $t'_j\,(t'_{c_Q(\mathcal C.\mathrm{placeMap}(P))})^{-1}$ lies both in $\mathcal C$.integers and in the valuation subring of $P$; for the index $i_Q$, whenever the ratio $t'_{i_Q}(t'_{c_Q})^{-1}$ (indices taken at $\mathcal C.\mathrm{placeMap}(P)$) is $\mathcal C$-integral, its residue minus the constant $\mathrm{evalAt}$ of that residue has order exactly $1$ at $\mathcal C.\mathrm{placeMap}(P)$; and for any two places $P, Q$ in $\mathcal C$.dom with distinct images, given integrality of all the corresponding ratios, there are indices $i, j$ with $\mathrm{evalAt}_P(\bar u_i)\,\mathrm{evalAt}_Q(\bar u_j) \ne \mathrm{evalAt}_P(\bar u_j)\,\mathrm{evalAt}_Q(\bar u_i)$, where $\bar u_i$ denotes the residue of the $i$-th ratio at the relevant pivot.
--
--   This is the small-prime instance ($p = 5, 7, 11$, where every supersingular $j$-invariant is $0$ or $1728$ and all nodes are wide) of the chart-data package for the rescaled good family on the zero-chart of the multiplicative covering of $X_0(p)$: rationality of places, nonvanishing pivots, integral and fibrewise regular ratios, a local uniformiser coming from one distinguished ratio, and separation of distinct reduced points by a $2\times 2$ minor of values. It is used by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le), which assembles the covering together with a certified family for all primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_lt_thirteen.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.MultCovering
open AlgebraicCurve

theorem ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_lt_thirteen (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hp13 : p < 13)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (hAd : ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      LinearIndependent (IsLocalRing.ResidueField ↥A)
        (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) := by sorry
