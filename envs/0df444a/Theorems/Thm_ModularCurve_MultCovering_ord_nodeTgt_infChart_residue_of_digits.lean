-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ord_nodeTgt_infChart_residue_of_digits
-- name    : ModularCurve.MultCovering.ord_nodeTgt_infChart_residue_of_digits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/fde3f45e-c51d-5b21-987e-03ecea3adf01
-- title:
--   Node orders of digit-recombined good family reductions
-- statement:
--   Let $p \ge 13$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ lies in the nonunits of $A$), with residue field $k := \mathrm{ResidueField}\,A$ of characteristic $p$, let $\Gamma$ be a chart context and $\Delta$ an annulus context for $\Gamma$, and let $\Phi$ be a good-family context of $r$ functions $\Phi.t_l$ at level $1\cdot p$, with Hasse exponents $n_l := \mathrm{hasseExp}\,\Phi.t_l$. Assume each $\Phi.t_l$ is integral for the chart $\mathrm{infChart}\,\Gamma$, and that polynomials $P_l \in k[X]$ are given with, for $l \ge 1$, $\deg P_l + 1 \le \mathrm{mAnnuli}\,p$ and residue $\overline{\Phi.t_l} = \mathrm{ssPolyBar}\,\Gamma \cdot P_l(\bar\jmath)$, where $\mathrm{ssPolyBar}\,\Gamma = \prod_e (\bar\jmath - a_e)$ with $a_e := \mathrm{ssValue}\,\Gamma\,e$ for $e \in \mathrm{Fin}(\mathrm{mAnnuli}\,p)$, and with the family $(P_l)_{l \ge 1}$ linearly independent over $k$. Let $d_{ij} \in \mathbb{Z}/p$ be digits, and let $t'_l$ be $\mathrm{infChart}\,\Gamma$-integral functions at level $1 \cdot p$ with $\overline{t'_l} = 1$ for $l = 0$ and, for $i \ge 1$, $\overline{t'_i} = \sum_j [\,n_i \le n_j\,]\,d_{ij}\,\overline{\Phi.t_j}$, the digit being taken as its natural-number representative in $k$ and pushed into $\mathrm{modularFunctionFieldC}\,k\,1$. Writing $N_i := \sum_{j} [\,1 \le j \wedge n_i \le n_j\,]\,d_{ij} \cdot P_j$ and $w_e := \mathrm{jWidth}(a_e)$ (so $w_e = 3$ if $a_e = 0$, $2$ if $a_e = 1728$, and $1$ otherwise), assume three avoidance hypotheses: $P_j(a_e) = 0$ whenever $j \ge 1$, $n_j = 2$ and $w_e = 1$; $N_i(a_e) \ne 0$ whenever $i \ge 1$ and either $w_e \ne 1$ or $n_i = 1$; and $N_i'(a_e) \ne 0$ whenever $i \ge 1$, $n_i = 2$ and $w_e = 1$. The conclusion is fourfold: every $\overline{t'_l}$ is nonzero; and for $l \ge 1$ the order of $\overline{t'_l}$ at the node $\mathrm{nodeTgt}\,\Gamma\,e$ (the geometric place of the target component attached to the point $\bar\jmath = a_e$) equals $1$ if $w_e \ne 1$, equals $1$ if $n_l = 1$, and equals $2$ if $n_l = 2$ and $w_e = 1$.
--
--   This records the $\bar\infty$-side order data of a digit-recombined good family on the two-component reduction of $X_0(p)$: non-vanishing of the reductions together with simple zeros at the wide nodes and at all nodes for members of Hasse exponent $1$, and double zeros at the width-one nodes for members of Hasse exponent $2$. It feeds the construction of unimodular good families with wide certificates ([`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates)), using that the supersingular polynomial is separable so that the order of $\mathrm{ss}\cdot Q(\bar\jmath)$ at the node above $a_e$ is $1 + \mathrm{mult}_{a_e}Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ord_nodeTgt_infChart_residue_of_digits.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ord_nodeTgt_infChart_residue_of_digits
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hintI : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (ResidueField ↥A))
    (hP : ∀ l : Fin r, 1 ≤ (l : ℕ) → (P l).natDegree + 1 ≤ mAnnuli p ∧
      (infChart Γ).residue ⟨Φ.t l, hintI l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l))
    (hPLI : LinearIndependent (ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l))
    (d : Fin r → Fin r → ZMod p)
    (t' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hintI' : ∀ l, t' l ∈ (infChart Γ).integers)
    (h0 : ∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨t' l, hintI' l⟩ = 1)
    (hres : ∀ i : Fin r, 1 ≤ (i : ℕ) → (infChart Γ).residue ⟨t' i, hintI' i⟩
      = ∑ j : Fin r, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
          (if hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j then ((d i j).val : ResidueField ↥A) else 0)
          * (infChart Γ).residue ⟨Φ.t j, hintI j⟩)

    (hav0 : ∀ (e : Fin (mAnnuli p)) (j : Fin r), 1 ≤ (j : ℕ) → hasseExp Φ.toFamData j = 2 →
      jWidth (ssValue Γ e) = 1 → (P j).eval (ssValue Γ e) = 0)
    (hav1 : ∀ (e : Fin (mAnnuli p)) (i : Fin r), 1 ≤ (i : ℕ) →
      (jWidth (ssValue Γ e) ≠ 1 ∨ hasseExp Φ.toFamData i = 1) →
      (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j
          then ((d i j).val : ResidueField ↥A) else 0) • P j).eval (ssValue Γ e) ≠ 0)
    (hav2 : ∀ (e : Fin (mAnnuli p)) (i : Fin r), 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 2 → jWidth (ssValue Γ e) = 1 →
      (Polynomial.derivative (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j
          then ((d i j).val : ResidueField ↥A) else 0) • P j)).eval (ssValue Γ e) ≠ 0) :
    (∀ l, (infChart Γ).residue ⟨t' l, hintI' l⟩ ≠ 0) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → jWidth (ssValue Γ e) ≠ 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 1) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 1) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 → jWidth (ssValue Γ e) = 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 2) := by sorry
