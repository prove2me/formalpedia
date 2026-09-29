-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth
-- name    : ModularCurve.MultCovering.FamData.t_zeroChart_of_orth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/de1744b8-e868-5f21-8d8b-4aa4decb4e70
-- title:
--   Smith identification on the ̄ 0-chart of X₀(p)⊗ k
-- statement:
--   Let $p\ge 5$ be a prime and let $D$ be a family datum `FamData p r`: elements $t_l$ ($l\in\mathrm{Fin}\,r$) of the geometric modular function field $\overline{\mathbb{Q}}$-model of level $1\cdot p$ together with rational models $t^{\mathrm{Rat}}_l$ in `modularFunctionFieldFull (1 * p)` whose coefficient embeddings are the $t_l$. Assume: $t_l=1$ for the index $l$ with $l=0$; the $t_l$ form an embedding basis, i.e. they are linearly independent over $\overline{\mathbb{Q}}$ and span the Riemann–Roch space of `embDivisor (1 * p)`; an orthonormality condition at $\bar\infty$, namely that for $c:\mathrm{Fin}\,r\to\mathbb{Q}$ all Laurent coefficients of $\sum_i c_i t^{\mathrm{Rat}}_i$ have non-negative $p$-adic valuation if and only if all $v_p(c_i)\ge 0$; the corresponding orthogonality condition for $\sum_i c_i\,w_p(t^{\mathrm{Rat}}_i)$, with $w_p$ the Fricke involution `frickeInvolutionFull (1 * p)`, now with the bounds $v_p(c_i)\ge -n_i$ where $n_i=$ `hasseExp D i`; and $n_l=0$ for $l=0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p\in A^{\mathrm{nonunits}}$ and residue field $k$ of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A`, let $\Delta$ be an annulus context over $\Gamma$, and assume each supersingular value $a_e=$ `ssValue Γ e` ($e\in\mathrm{Fin}(\mathrm{mAnnuli}\,p)$) satisfies $a_e\ne 0$ and $a_e\ne 1728$. Then each $t'_l:=p^{-n_l}t_l$ (`goodFamilyZero D l`) lies in the integers of the chart `zeroChart Γ`, the pullback of `infChart Γ` along the Fricke involution of the geometric field, and there are polynomials $P_l\in k[X]$ with $\deg P_l\le m:=$ `mAnnuli p`, linearly independent over $k$, spanning all polynomials of degree $\le m$, with $P_l=\prod_e\bigl(X-a_e^{\,p}\bigr)$ for $l=0$, such that for every $l$ the residue of $t'_l$ on `zeroChart Γ`, multiplied by `ssPolyBarZero Γ` $=\prod_e\bigl(\bar j-a_e^{\,p}\bigr)$, equals $P_l(\bar j)$, where $\bar j$ is the class of the $j$-function in the level-one function field over $k$.
--
--   This is the $\bar 0$-side half of the construction of the good-family context for the multiplicative covering of $X_0(p)$ at $p$, identifying the reductions of the normalised family members on the component of $X_0(p)\otimes k$ carrying the coordinate $\bar j$ with polynomials of degree at most the number of supersingular $j$-invariants, under the width-one hypothesis on all nodes. It is used by [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering
open ModularCurve hiding jBar

theorem ModularCurve.MultCovering.FamData.t_zeroChart_of_orth
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (D : FamData p r)
    (hzero  : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hexp0 : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp D l = 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers)
      (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
      (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
      LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
      (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
        Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 →
        P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ * ssPolyBarZero Γ
        = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := by sorry
