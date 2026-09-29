-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent
-- name    : ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b8e25054-3993-56b5-84c5-97a08393053a
-- title:
--   Chart data on the ̄0-chart from independent reductions
-- statement:
--   Let $p$ be a prime with $13\le p$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, write $k$ for the residue field of $A$ and assume $\operatorname{char} k = p$; let $\Gamma$ be a chart context `ChartCtx p A` for the prime-level multiplicative covering, and let $\Phi$ be a family context `FamCtx p r`, that is, a `FamData p r` whose members $t_l$ form an embedding basis at level $1\cdot p$, are normalised by $t_l=1$ for $l=0$, and satisfy the prescribed integrality and reduction conditions on the $\bar\infty$- and $\bar0$-charts. Put $C:=$ `zeroChart Γ`, the component chart obtained from the $\bar\infty$-chart of $\Gamma$ by comap along `frickeInvolutionBar (1 * p)`, whose reductions lie in `modularFunctionFieldC k 1`, and put $u_l:=$ `goodFamilyZero Φ.toFamData l` $=\bigl(p^{\mathrm{hasseExp}\,\Phi\,l}\bigr)^{-1}t_l$ in `modularFunctionFieldBar (1 * p)`. Assume each $u_l$ lies in $C$`.integers` and that the $r$ reductions $C$`.residue` $u_l$ are linearly independent over $k$. The conclusion asserts the existence of the integrality witness again together with two maps $c,i$ from the places of `modularFunctionFieldC k 1` over $k$ to `Fin r` such that: (i) every $P\in C$`.dom` and its image $\bar P:=C$`.placeMap` $P$ are rational places, i.e. the structure map of the base field onto the residue field of the place is surjective; (ii) the reduction of $u_{c(\bar P)}$ is non-zero for every $P\in C$`.dom`; (iii) for all such $P$ and all $j$, the ratio $u_j\,u_{c(\bar P)}^{-1}$ lies in $C$`.integers`; (iv) and also in the valuation ring of $P$; (v) for all such $P$ and any witness that $u_{i(\bar P)}u_{c(\bar P)}^{-1}$ is $C$-integral, the reduction of this ratio minus the constant $\mathrm{evalAt}_{\bar P}$ of that reduction has `Place.ord` exactly $1$ at $\bar P$; and (vi) for $P,Q\in C$`.dom` with $\bar P\ne\bar Q$, and given that all ratios $u_j u_{c(\bar P)}^{-1}$ and $u_j u_{c(\bar Q)}^{-1}$ are $C$-integral, there are indices $i,j$ for which the corresponding $2\times2$ minor of the values at $\bar P$ and $\bar Q$ of the reduced ratios is non-zero.
--
--   This is the width-free chart-data statement for the $\bar0$-chart of the multiplicative covering of $X_0(p)$, the Fricke-twisted companion of the $\bar\infty$-chart version: from linear independence of the reductions of the rescaled family $p^{-n_l}t_l$ it produces the normalising and separating index data (non-vanishing leading member, integral ratios, a ratio that is a uniformiser after subtracting its value, and a non-vanishing $2\times2$ minor separating distinct images of places), with no hypothesis on the widths of the nodes. It feeds the uniform construction of a multiplicative covering with a certified family in [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent.lean

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

theorem ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
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
