-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven
-- name    : ModularCurve.MultCovering.exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b31a2e19-0495-5f44-88ba-25619aa93e3b
-- title:
--   Unimodular recombination with attained node orders at p=11
-- statement:
--   Fix a prime $p$ with $p=11$, a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ (i.e. $p$ is a non-unit of $A$), with the residue field of $A$ of characteristic $p$ and decidable equality, chart data $\Gamma : \mathrm{ChartCtx}\ p\ A$, annulus data $\Delta : \mathrm{AnnCtx}\ \Gamma$, a natural number $r$, and a family context $\Phi : \mathrm{FamCtx}\ p\ r$. Assume that each rescaled member $\mathrm{goodFamilyZero}\ \Phi_l = (p^{n_l})^{-1}\Phi.t_l$, with $n_l := \mathrm{hasseExp}\ \Phi\ l$, lies in the integers of the chart `zeroChart Γ`, and that their residues in the residue field of $A$ are linearly independent. Then there are a matrix $U$ over $\mathbb Q$ of size $r$, a family $D' : \mathrm{FamData}\ p\ r$ and integrality witnesses for the rescaled members of $D'$ such that: $U$ is a unit; for all $i,j$ either $U_{ij}=0$ or $v_p(U_{ij})\ge\max(0,n_i-n_j)$, and likewise for $U^{-1}$; the row of $U$ with index $0$ is the $0$th standard basis vector; $D'.tRat_i=\sum_j U_{ij}\Phi.tRat_j$ and correspondingly $D'.t_i=\sum_j U_{ij}\Phi.t_j$ after base change to $\overline{\mathbb Q}$; $\mathrm{hasseExp}\ D' = \mathrm{hasseExp}\ \Phi$ termwise; $\mathrm{goodFamilyZero}\ D'_l = (p^{n_l})^{-1}\sum_j U_{lj}\Phi.t_j$; the new `zeroChart Γ` residues are still linearly independent; and for every annulus index $e < \mathrm{mAnnuli}\ p$ and every $l$, the order of that residue at the place $\mathrm{nodeSrc}\ \Gamma\ e$ attached to $(\mathrm{ssValue}\ \Gamma\ e)^p$ equals $-\lfloor n_l / \mathrm{jWidth}(\mathrm{ssValue}\ \Gamma\ e)\rfloor$, where $\mathrm{jWidth}(j)$ is $3$ for $j=0$, $2$ for $j=1728$ and $1$ otherwise.
--
--   This is the $p=11$ case of the recombination step in the construction of a uniform multiplicative covering of the modular curve: a rational change of basis of the family, compatible with the $p$-adic filtration given by the Hasse exponents and normalised in its zeroth row, after which the orders of the reduced members at the supersingular nodes of the source component are exactly the expected floors $-\lfloor n_l/w_e\rfloor$. It feeds the prime-by-prime assembly in [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le), where $p=11$ (for which $\mathrm{mAnnuli}\ 11$ counts nodes at $j=0$ of width $3$ and $j=1728$ of width $2$) needs a genuine recombination rather than the identity matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven
    (p : ℕ) [Fact p.Prime] (hp11 : p = 11) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers),
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
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)
          = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) := by sorry
