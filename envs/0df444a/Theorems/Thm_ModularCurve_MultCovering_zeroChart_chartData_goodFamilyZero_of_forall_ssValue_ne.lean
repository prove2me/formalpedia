-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
-- name    : ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/850ea803-9268-58b5-b8d4-118571986856
-- title:
--   Chart data on the ̄ 0-chart when all nodes have width one
-- statement:
--   Let $p$ be a prime and $A$ a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $A$, with residue field $k$ of characteristic $p$; let $\Gamma$ be a chart context `ChartCtx p A` for the prime-level multiplicative covering, and let $\Phi$ be a family context `FamCtx p r` for some $r$. Assume that every supersingular value $\mathrm{ssValue}\ \Gamma\ e$ is different from $0$ and from $1728$. Write $C = \mathrm{zeroChart}\ \Gamma$, the component chart obtained from $\mathrm{infChart}\ \Gamma$ by pulling back along the Fricke involution of level $1\cdot p$, and $t'_l = p^{-\mathrm{hasseExp}\,\Phi\,l}\cdot \Phi.t\ l$ for the rescaled family members $\mathrm{goodFamilyZero}$. The assertion is that all $t'_l$ lie in the valuation subring $C.\mathrm{integers}$, and that there exist maps $c$ and $i$ from the places of $\mathrm{modularFunctionFieldC}\ k\ 1$ over $k$ to $\mathrm{Fin}\ r$ such that, for every place $P$ in $C.\mathrm{dom}$, writing $\bar P = C.\mathrm{placeMap}\ P$: both $P$ and $\bar P$ are rational (the structure map onto the residue field is surjective); the residue $\overline{t'_{c(\bar P)}}$ is nonzero; for every $j$ the ratio $t'_j\,(t'_{c(\bar P)})^{-1}$ lies both in $C.\mathrm{integers}$ and in the valuation subring of $P$; the reduction of $t'_{i(\bar P)}(t'_{c(\bar P)})^{-1}$ minus the constant given by its value $\mathrm{evalAt}$ at $\bar P$ has $\mathrm{ord}$ equal to $1$ at $\bar P$; and for any two places $P,Q$ in $C.\mathrm{dom}$ with $\bar P \neq \bar Q$ (and all the above ratios integral for both pivots) there are indices $i,j$ for which the $2\times 2$ minor of the evaluated reduced ratios at $\bar P$ and $\bar Q$ is nonzero.
--
--   This is the $\bar 0$-chart case, under the hypothesis that no supersingular $j$-invariant equals $0$ or $1728$, of the package of chart data (pivot index, integral fibre-regular ratios, immersion index, separating minor) attached to a rescaled good family on a component chart of the multiplicative covering of $X_0(p)$. It feeds the construction of a uniform multiplicative covering with a certified family for primes $p \geq 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering
open ModularCurve

theorem ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
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
