-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates
-- name    : ModularCurve.MultCovering.exists_hasseExp_eq_one_unramified_and_separates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/05201109-d002-5efd-ac20-1d610d2e3cd0
-- title:
--   Content-one witnesses at wide nodes on the zero chart
-- statement:
--   Fix a prime $p$ with $13 \le p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ (that is, $p$ lies in the non-units of $A$), with residue field $k = \mathrm{ResidueField}\,A$ of characteristic $p$ and decidable equality; let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$ and $\Delta$ an annulus context `AnnCtx` over $\Gamma$ (two families of annuli indexed by `Fin (mAnnuli p)`, with equal domains and non-zero moduli, parameters multiplying to the modulus $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$, domains the places supersingularly centred at $\mathrm{ssValue}\,\Gamma\,e$, and attachments to the source and target charts at the nodes `nodeSrc`, `nodeTgt`). Let $\Phi$ be a family context `FamCtx p r` with members $t_l$, $l \in$ `Fin r`, and put $t'_l = (p^{\,\mathrm{hasseExp}\,\Phi\,l})^{-1} t_l$ (`goodFamilyZero`). Assume each $t'_l$ is integral for the chart `zeroChart Γ` and that the reductions $\bar t'_l \in \mathrm{modularFunctionFieldC}\,k\,1$ are linearly independent over $k$. Let $e$ be an annulus index with $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e) \ne 1$, i.e. $\mathrm{ssValue}\,\Gamma\,e \in \{0, 1728\}$. Then: (i) there are $l$ with $\mathrm{hasseExp}\,\Phi\,l = 1$ and $c \in k$ such that $\bar t'_l - c$ has $\mathrm{ord} = 1$ at the place $\mathrm{nodeSrc}\,\Gamma\,e$ (the place attached to the point $(\mathrm{ssValue}\,\Gamma\,e)^p$); and (ii) for every $e' \ne e$ with $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e') \ne 1$ there is $l$ with $\mathrm{hasseExp}\,\Phi\,l = 1$ whose reduction $\bar t'_l$ takes different values at $\mathrm{nodeSrc}\,\Gamma\,e$ and at $\mathrm{nodeSrc}\,\Gamma\,e'$ (values in $k$, via `Place.evalAt`).
--
--   This is the non-emptiness statement on the $\bar 0$-chart side of the multiplicative covering of $X_0(p)$: among the members of the family of content (Hasse exponent) exactly one, some member has a simple zero at a prescribed wide node after subtraction of a constant, and some member separates any two distinct wide nodes. It is used by [`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates) in the genericity step producing unimodular family data with certificates at the wide annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_hasseExp_eq_one_unramified_and_separates
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (he : jWidth (ssValue Γ e) ≠ 1) :
    (∃ l : Fin r, hasseExp Φ.toFamData l = 1 ∧ ∃ c : ResidueField ↥A,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩
          - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1) ∧
    (∀ e' : Fin (mAnnuli p), e' ≠ e → jWidth (ssValue Γ e') ≠ 1 →
      ∃ l : Fin r, hasseExp Φ.toFamData l = 1 ∧
        (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
          ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) := by sorry
