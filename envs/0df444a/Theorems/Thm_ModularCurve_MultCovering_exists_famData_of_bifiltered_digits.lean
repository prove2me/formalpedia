-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits
-- name    : ModularCurve.MultCovering.exists_famData_of_bifiltered_digits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/3c7de00f-83f3-555a-ae31-ae712c1782d4
-- title:
--   Recombining a good family by a bi-filtered digit matrix
-- statement:
--   Let $p \ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ and residue field $k$ of characteristic $p$, let $\Gamma$ be a chart context for the covering at level $1\cdot p$ over $A$ (providing the charts `infChart` $\Gamma$ and `zeroChart` $\Gamma$ with values in $k$-subfields of Laurent series), and let $\Delta$ be an annulus context over $\Gamma$. Let $\Phi$ be a family context of rank $r$, so in particular a family $t_l \in \overline{\mathbb Q}$-rational modular function field of level $1\cdot p$ arising by coefficient extension from rational members $t^{\mathrm{rat}}_l$, with contents $n_l =$ `hasseExp` $\Phi\, l$. Assume each $t_l$ lies in the integers of the $\bar\infty$-chart, each rescaled member $p^{-n_l} t_l$ lies in the integers of the $\bar 0$-chart, and the $\bar 0$-residues of the $p^{-n_l}t_l$ are linearly independent over $k$. Let $U \in M_r(\mathbb Q)$ be invertible and $d_{ij} \in \mathbb Z/p$ be such that each entry of $U$ and of $U^{-1}$ is either $0$ or of $p$-adic valuation at least $\max(0, n_i - n_j)$, the $0$-th row of $U$ is the first standard basis vector, $U_{ij} = p^{\max(0,n_i-n_j)}\cdot \widetilde{d_{ij}}$ with $\widetilde{d_{ij}} \in \{0,\dots,p-1\}$ the canonical lift, and for every $c$ the determinant of the block $(d_{ij})_{n_i = n_j = c}$ is a unit. Then there is family data $D'$ of rank $r$, together with witnesses that each $p^{-n'_l}D'.t_l$ is $\bar 0$-integral and each $D'.t_l$ is $\bar\infty$-integral, such that: $D'.t^{\mathrm{rat}}_i = \sum_j U_{ij} t^{\mathrm{rat}}_j$ and $D'.t_i = \sum_j U_{ij} t_j$; the contents are unchanged, `hasseExp` $D'\, l = n_l$; the rescaled members are $p^{-n_l}\sum_j U_{lj} t_j$; the $\bar 0$-residues of the rescaled members of $D'$ remain $k$-linearly independent; and the two read-off formulas hold, namely the $\bar\infty$-residue of $D'.t_i$ equals $\sum_j [n_i \le n_j]\, d_{ij}$ times the $\bar\infty$-residue of $t_j$, and the $\bar 0$-residue of $p^{-n_i}D'.t_i$ equals $\sum_j [n_j \le n_i]\, d_{ij}$ times the $\bar 0$-residue of $p^{-n_j}t_j$, the digits entering through the structural map of $k$ into the characteristic-$p$ modular function field of level $1$.
--
--   This is the recombination step for good families on the multiplicative covering of $X_0(p)$: a matrix given in digit form, compatible with the bi-filtration by Hasse contents, transforms a good family into a new one preserving both the $\bar\infty$- and the $\bar 0$-integral structures, with the reductions on the two charts read off from the digits by the two triangularity conditions $n_i \le n_j$ and $n_j \le n_i$. It is used in the construction of unimodular family data with wide certificates, including the special case $p = 11$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_famData_of_bifiltered_digits
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hintI : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p)
    (hUunit : IsUnit U)
    (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
      ∨ U i j = 0)
    (hUinv : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
      ∨ U⁻¹ i j = 0)
    (hU0 : ∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0)
    (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))).toNat
      * ((d i j).val : ℚ))
    (hblock : ∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // hasseExp Φ.toFamData a = c}) => d i.1 j.1))) :
    ∃ (D' : FamData p r) (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers),
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      (∀ i, (infChart Γ).residue ⟨D'.t i, hintI' i⟩
          = ∑ j, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
              (if hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j then ((d i j).val : ResidueField ↥A) else 0)
              * (infChart Γ).residue ⟨Φ.t j, hintI j⟩) ∧
      (∀ i, (zeroChart Γ).residue ⟨goodFamilyZero D' i, hint' i⟩
          = ∑ j, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
              (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
              * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩) := by sorry
