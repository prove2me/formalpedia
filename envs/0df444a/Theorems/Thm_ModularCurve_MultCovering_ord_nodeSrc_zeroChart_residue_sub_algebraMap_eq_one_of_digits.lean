-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
-- name    : ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/922b3cff-a140-549c-8e83-743d583d9f52
-- title:
--   Simple value at a width-three node after digit recombination
-- statement:
--   Let $p$ be a prime with $13 \le p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ is a non-unit of $A$), and write $k$ for the residue field of $A$, assumed of characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$, $\Delta$ an annulus context over $\Gamma$, and $\Phi$ a family context of rank $r$ for $p$; put $\rho_j :=$ the residue, in the zero chart of $\Gamma$ with values in $\mathrm{modularFunctionFieldC}\,k\,1$, of the rescaled member $\mathrm{goodFamilyZero}\,\Phi\,j = p^{-\mathrm{hasseExp}\,\Phi\,j}\,t_j$, these members being assumed integral for the zero chart. Let $d : \mathrm{Fin}\,r \to \mathrm{Fin}\,r \to \mathbb{Z}/p$ be digits and let $g'_i$ be elements of $\mathrm{modularFunctionFieldBar}(1\cdot p)$, integral for the zero chart, whose residues satisfy $\overline{g'_i} = \sum_j \delta_{ij}\,\rho_j$, where $\delta_{ij}$ is the image in the function field of the representative $(d_{ij})_{\mathrm{val}} \in k$ when $\mathrm{hasseExp}\,\Phi\,j \le \mathrm{hasseExp}\,\Phi\,i$ and $0$ otherwise. Let $e$ be an index of an annulus with $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e) = 3$, equivalently $\mathrm{ssValue}\,\Gamma\,e = 0$, and let $x_e := \mathrm{nodeSrc}\,\Gamma\,e$ be the geometric place of $\mathrm{modularFunctionFieldC}\,k\,1$ attached to the point $(\mathrm{ssValue}\,\Gamma\,e)^p$. Let $a, w : \mathrm{Fin}\,r \to k$ be such that, for every $j$ with $\mathrm{hasseExp}\,\Phi\,j \le 1$, the place $x_e$ has value $a_j$ at $\rho_j$ and value $w_j$ at $(\rho_j - a_j)\,(\bar{\jmath} - (\mathrm{ssValue}\,\Gamma\,e)^p)^{-1}$, where $\bar{\jmath}$ is the class of $\mathrm{jqModC}\,k$ and 'has value $c$' means membership in the valuation subring of the place together with residue $c$. Assume finally that for every $i$ with $1 \le i$ and $\mathrm{hasseExp}\,\Phi\,i = 1$ one has $\sum_j \delta'_{ij} w_j \ne 0$, with $\delta'_{ij}$ the same digit pattern taken in $k$. Then for every such $i$ there exists $c \in k$ with $\mathrm{ord}_{x_e}(\overline{g'_i} - c) = 1$.
--
--   This is the unramified-value certificate at a node of width three (the node above $j = 0$) for the digit-recombined members of a good family on $X_0(p)$: value and first-order value at the node are additive and $k$-linear, so the recombined reduction takes its value to exact order one precisely when the recombined first-order functional is non-zero. It is used in the construction of wide certificates, being cited by [`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (d : Fin r → Fin r → ZMod p)
    (g' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hint' : ∀ l, g' l ∈ (zeroChart Γ).integers)
    (hres0 : ∀ i : Fin r, (zeroChart Γ).residue ⟨g' i, hint' i⟩
      = ∑ j : Fin r, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
          (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
          * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)
    (e : Fin (mAnnuli p)) (he : jWidth (ssValue Γ e) = 3)

    (a w : Fin r → ResidueField ↥A)
    (ha : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩) (a j))
    (hw : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue
        (((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩
            - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (a j))
          * ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
              - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (ssValue Γ e ^ p))⁻¹)
        (w j))

    (hunr : ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * w j) ≠ 0) :
    ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      ∃ c : ResidueField ↥A,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨g' i, hint' i⟩
          - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1 := by sorry
