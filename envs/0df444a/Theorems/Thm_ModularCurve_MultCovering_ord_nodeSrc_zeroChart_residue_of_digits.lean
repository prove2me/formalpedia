-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_of_digits
-- name    : ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_of_digits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/dd1faaf5-10a9-57a9-90dd-6c46905d3a3b
-- title:
--   Node order and separation for a digit recombination on the ̄0-chart
-- statement:
--   Fix a prime $p$ with $13\le p$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (so $A$ lies over $p$) and residue field $k$ of characteristic $p$, a chart context $\Gamma$ for the multiplicative covering at level $1\cdot p$, an annulus context $\Delta$ over $\Gamma$, and a good-family context $\Phi$ of rank $r$, i.e. a family $(t_l)_{l<r}$ in $\overline{\mathbb Q}$-level modular functions of level $1\cdot p$ together with the basis and chart data of `FamCtx`. Write $n_l=$ `hasseExp Φ.toFamData l` and $\bar g_l$ for the `zeroChart Γ`-residue in `modularFunctionFieldC k 1` of the rescaled element `goodFamilyZero Φ.toFamData l` $=p^{-n_l}t_l$, assumed integral for the $\bar0$-chart by `hint`. Let $d_{ij}\in\mathbb Z/p$ be digits, let $g'_i$ be $\bar0$-chart integral elements, and assume the read-off formula $\overline{g'_i}=\sum_{j}\kappa_{ij}\,\bar g_j$, where $\kappa_{ij}\in k$ is the image of the canonical representative of $d_{ij}$ when $n_j\le n_i$ and $0$ otherwise. For $e<$ `mAnnuli p` put $a_e=$ `ssValue Γ e`, $w_e=$ `jWidth` $a_e$ (namely $3$, $2$ or $1$ according as $a_e=0$, $a_e=1728$, or otherwise), and let $x_e=$ `nodeSrc Γ e` be the place of the function field attached to the point $\tilde\jmath=a_e^{\,p}$. Assume: (regularity) $\bar g_j$ lies in the valuation subring of $x_e$ whenever $n_j<w_e$; (value avoidance) $\sum_j\kappa_{ij}\,\bar g_j(x_e)\ne0$ for all $e$ with $w_e\ne1$ and all $i$ with $n_i<w_e$, the evaluation being `Place.evalAt`; (separation) $\sum_j\kappa_{ij}\bigl(\bar g_j(x_e)-\bar g_j(x_{e'})\bigr)\ne0$ for $e\ne e'$ with $w_e,w_{e'}\ne1$ and $i\ge1$ with $n_i=1$. The conclusion is twofold: $\operatorname{ord}_{x_e}\overline{g'_i}=0$ whenever $w_e\ne1$ and $n_i<w_e$; and $\overline{g'_i}(x_e)\ne\overline{g'_i}(x_{e'})$ for $e\ne e'$ with $w_e,w_{e'}\ne1$ and $i\ge1$, $n_i=1$.
--
--   This is the place-evaluation step that converts numerical non-vanishing conditions on a digit recombination into geometric information on the $\bar0$-chart of the multiplicative covering: unit order at the wide supersingular nodes and pairwise separation of node values. It is used in the construction of unimodular family data with wide certificates ([`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_of_digits.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_of_digits
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

    (hreg : ∀ (e : Fin (mAnnuli p)) (j : Fin r), hasseExp Φ.toFamData j < jWidth (ssValue Γ e) →
      (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ ∈ (nodeSrc Γ e).toValuationSubring)

    (hz : ∀ (e : Fin (mAnnuli p)) (i : Fin r), jWidth (ssValue Γ e) ≠ 1 → hasseExp Φ.toFamData i < jWidth (ssValue Γ e) →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)) ≠ 0)
    (hsep : ∀ (e e' : Fin (mAnnuli p)) (i : Fin r), e ≠ e' → jWidth (ssValue Γ e) ≠ 1 → jWidth (ssValue Γ e') ≠ 1 →
      1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * ((nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)
           - (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩))) ≠ 0) :
    (∀ (e : Fin (mAnnuli p)) (i : Fin r), jWidth (ssValue Γ e) ≠ 1 → hasseExp Φ.toFamData i < jWidth (ssValue Γ e) →
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨g' i, hint' i⟩) = 0) ∧
    (∀ (e e' : Fin (mAnnuli p)) (i : Fin r), e ≠ e' → jWidth (ssValue Γ e) ≠ 1 → jWidth (ssValue Γ e') ≠ 1 →
      1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨g' i, hint' i⟩)
        ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨g' i, hint' i⟩)) := by sorry
