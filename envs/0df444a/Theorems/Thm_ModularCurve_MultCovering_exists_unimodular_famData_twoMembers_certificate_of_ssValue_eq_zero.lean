-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
-- name    : ModularCurve.MultCovering.exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/41d2ab66-8ba7-561f-9857-c0bca66f36bf
-- title:
--   Two-member certificate at a supersingular node with j=0
-- statement:
--   Let $p$ be a prime with $13 \le p$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ (i.e. $p$ lies in `A.nonunits`) whose residue field has characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` for the multiplicative covering of level $1\cdot p$ and $\Delta$ an annulus context for $\Gamma$, and let $\Phi$ be a family context `FamCtx p r` with members $\Phi.t_l \in \overline{\mathbb Q}\text{-}$span data and rational forms $\Phi.\mathrm{tRat}_l$. Write $n_l =$ `hasseExp Φ.toFamData l` (the $p$-adic content exponent of the $l$-th member, the truncation to $\mathbb N$ of the least $p$-adic valuation among the coefficients of its associated Laurent series) and `goodFamilyZero Φ.toFamData l` $= (p^{n_l})^{-1}\Phi.t_l$. Assume each `goodFamilyZero Φ.toFamData l` lies in the integers of the chart `zeroChart Γ` and that their residues are linearly independent over the residue field of $A$, and let $e$ be an index of an annulus with `ssValue Γ e = 0`. Then there exist a matrix $U \in \mathrm{Mat}_r(\mathbb Q)$, family data $D' :$ `FamData p r`, witnesses that each `goodFamilyZero D' l` lies in the integers of `zeroChart Γ` and each $D'.t_l$ in the integers of `infChart Γ`, and indices $l_1, l_2$, such that: $U$ is invertible; for all $i,j$ either $U_{ij}=0$ or $\max(0, n_i-n_j) \le v_p(U_{ij})$, and likewise for the entries of $U^{-1}$; $U_{0j} = \delta_{0j}$; $D'.\mathrm{tRat}_i = \sum_j U_{ij}\,\Phi.\mathrm{tRat}_j$ and $D'.t_i = \sum_j U_{ij}\,\Phi.t_j$ (entries transported by $\mathbb Q \to \overline{\mathbb Q} \to$ the function field); `hasseExp D' l` $= n_l$ for all $l$, so that `goodFamilyZero D' l` $= (p^{n_l})^{-1}\sum_j U_{lj}\Phi.t_j$; the residues of the `goodFamilyZero D' l` in `zeroChart Γ` are again linearly independent over the residue field of $A$; $1 \le l_1$ and $1 \le l_2$; the residues of $D'.t_{l_1}$ and $D'.t_{l_2}$ in `infChart Γ` each have order $1$ at the place `nodeTgt Γ e`; the residue of `goodFamilyZero D' l₁` in `zeroChart Γ` has order $0$ at `nodeSrc Γ e` and that of `goodFamilyZero D' l₂` has order $\le 0$ there; $n_{l_1} < n_{l_2}$; and for every place $Q$ in the domain of `zeroChart Γ`, the value of the residue of `goodFamilyZero D' l₁` at `(zeroChart Γ).placeMap Q` differs from its value at `nodeSrc Γ e`.
--
--   This is the two-member separation certificate at an annulus whose supersingular $j$-invariant is $0$: a unimodular, content-filtered recombination of a good family producing two members with prescribed orders at the two ends of the annulus, distinct content exponents, and a reduced first member separating the node from all places of the zero-chart's domain. It is used by [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted) in the cross-comparison of the two charts across the annuli of the multiplicative covering of $X_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (he : ssValue Γ e = 0) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers) (l₁ l₂ : Fin r),
      IsUnit U ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
        ∨ U i j = 0) ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
        ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      1 ≤ (l₁ : ℕ) ∧ 1 ≤ (l₂ : ℕ) ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₁, hintI' l₁⟩) = 1 ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₂, hintI' l₂⟩) = 1 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) = 0 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₂, hint' l₂⟩) ≤ 0 ∧
      hasseExp D' l₁ < hasseExp D' l₂ ∧
      ∀ Q ∈ (zeroChart Γ).dom,
        ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩)
          ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) := by sorry
