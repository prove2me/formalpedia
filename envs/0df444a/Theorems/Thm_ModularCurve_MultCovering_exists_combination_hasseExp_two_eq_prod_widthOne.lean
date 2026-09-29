-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_combination_hasseExp_two_eq_prod_widthOne
-- name    : ModularCurve.MultCovering.exists_combination_hasseExp_two_eq_prod_widthOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/2c586e17-2d38-5f9d-b7a2-67e64879f739
-- title:
--   Content-two members combine to the width-one node product
-- statement:
--   Let $p$ be a prime with $13 \le p$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ (that is, $p$ is a nonunit of $A$), with residue field $k := \mathrm{ResidueField}\,A$ of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` for the covering, $\Delta$ an annulus context `AnnCtx` over $\Gamma$, and $\Phi$ a good-family context `FamCtx p r` with members $t_l =$ `goodFamily` $\Phi\,l$, $l \in \mathrm{Fin}\,r$. Assume: each rescaled member `goodFamilyZero` $\Phi\,l = (p^{\mathrm{hasseExp}\,\Phi\,l})^{-1} t_l$ lies in the integers of the chart `zeroChart` $\Gamma$ (the Fricke pullback of `infChart` $\Gamma$) and their residues are $k$-linearly independent; and some annulus index $e$ has $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e) \neq 1$, i.e. its supersingular $j$-invariant is $0$ or $1728$. Then, for every proof that all $t_l$ lie in the integers of `infChart` $\Gamma$ and every family $P : \mathrm{Fin}\,r \to k[X]$ such that for $l \ge 1$ one has $\deg P_l + 1 \le \mathrm{mAnnuli}\,p$ and the `infChart` residue of $t_l$ equals $\mathrm{ssPolyBar}\,\Gamma \cdot P_l(\bar j)$, the $P_l$ ($l \ge 1$) being $k$-linearly independent, there exist scalars $c_l \in k$ vanishing unless $\mathrm{hasseExp}\,\Phi\,l = 2$ with $\sum_l c_l P_l = \prod_{e : \mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e) = 1} (X - \mathrm{ssValue}\,\Gamma\,e)$.
--
--   This is the census step in the analysis of the multiplicative (two-component) reduction of $X_0(p)$ at $p$: the members of the good family whose Hasse content equals $2$ have $\infty$-chart polynomials that span, among themselves, the product over the width-one supersingular nodes. It feeds the minimality and certificate statements [`ModularCurve.MultCovering.exists_rootMultiplicity_ssValue_minimal`](thm.html#ModularCurve.MultCovering.exists_rootMultiplicity_ssValue_minimal), [`ModularCurve.MultCovering.exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero) and [`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_combination_hasseExp_two_eq_prod_widthOne.lean

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

theorem ModularCurve.MultCovering.exists_combination_hasseExp_two_eq_prod_widthOne
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (hwide : ∃ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≠ 1) :
    ∀ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (P : Fin r → Polynomial (ResidueField ↥A)),
      (∀ l : Fin r, 1 ≤ (l : ℕ) → (P l).natDegree + 1 ≤ mAnnuli p ∧
        (infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l)) →
      LinearIndependent (ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) →
      ∃ c : Fin r → ResidueField ↥A, (∀ l, c l ≠ 0 → hasseExp Φ.toFamData l = 2) ∧
        ∑ l, c l • P l = ∏ e ∈ Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1),
          (Polynomial.X - Polynomial.C (ssValue Γ e)) := by sorry
