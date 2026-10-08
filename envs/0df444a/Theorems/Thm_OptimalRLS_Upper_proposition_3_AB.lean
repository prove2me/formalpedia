-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_3_AB
-- name    : OptimalRLS.Upper.proposition_3_AB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:26:19.943895+00:00
-- url     : https://prove2.me/theorems/ba83b5d7-176c-47c2-b259-bee5620da749
-- title:
--   Proposition 3, p. 18 — for ρ ∈ P(b, c): A(λ) ≤ λ^c ‖T^((1−c)/2) f_H‖² and B(λ) ≤ λ^(c−1) ‖T^((1−c)/2) f_H‖²
-- statement:
--   Let $1<b<+\infty$, $1\le c\le2$ and $\rho\in\mathcal P(b,c)$: $f_{\mathcal H}$ is the minimal-norm minimizer, Hypothesis 2 holds with $M,\Sigma$, $T=\sum_nt_n\langle\cdot,e_n\rangle e_n$ with $t_1\ge t_2\ge\cdots>0$ and $\alpha\le n^bt_n\le\beta$, and $f_{\mathcal H}=T^{(c-1)/2}g$ with $\|g\|_{\mathcal H}^2\le R$. Then for every $\lambda>0$, with $f^\lambda$ the minimizer of the regularized expected risk,
--   $$\mathcal A(\lambda)=\mathcal E[f^\lambda]-\mathcal E[f_{\mathcal H}]\le\lambda^c\,\big\|T^{\frac{1-c}2}f_{\mathcal H}\big\|_{\mathcal H}^2,\qquad\mathcal B(\lambda)=\|f^\lambda-f_{\mathcal H}\|_{\mathcal H}^2\le\lambda^{c-1}\,\big\|T^{\frac{1-c}2}f_{\mathcal H}\big\|_{\mathcal H}^2,$$
--   where $\|T^{\frac{1-c}2}f_{\mathcal H}\|_{\mathcal H}^2=\sum_n\langle g,e_n\rangle_{\mathcal H}^2\le\|g\|_{\mathcal H}^2\le R$.
--
--   These are the approximation-error rates that, inserted in Theorem 4, give the bias part of the rate of Theorem 1.
--
--   **Formalization Note** The clauses of Definition 1 are hypotheses of the theorem rather than packaged in `InPrior`, so that the right-hand side can name $g$ and the eigen-system. Since $f_{\mathcal H}=T^{(c-1)/2}g$, $T^{(1-c)/2}f_{\mathcal H}$ is the projection of $g$ onto $(\ker T)^\perp$, whose squared norm is $\sum_n\langle g,e_n\rangle^2$. The eigen-system is indexed from $0$ (the paper's $t_n$ is `t (n-1)`).
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 3 (A and B), p. 18; A, B, p. 13

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Proposition 3, bounds on `A(λ)` and `B(λ)`** (p. 18). Let `ρ ∈ P(b, c)` with `1 < b < +∞`,
`1 ≤ c ≤ 2` (the clauses of Definition 1 are unpacked: `f_H`, the eigen-system `(e, t)`, and `g` with
`f_H = T^{(c−1)/2} g`, `‖g‖² ≤ R`). For `λ > 0` and `f^λ` the minimizer of the regularized expected
risk, `A(λ) ≤ λ^c ‖T^{(1−c)/2} f_H‖²_H` and `B(λ) ≤ λ^{c−1} ‖T^{(1−c)/2} f_H‖²_H`, where
`‖T^{(1−c)/2} f_H‖²_H = ∑_n ⟨g, e_n⟩²` (the squared norm of the projection of `g` onto `(ker T)^⊥`). -/
theorem proposition_3_AB
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β b c : ℝ) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] (fH : H)
    (hfH : IsMinNormMinimizer ρ fH) (h2 : Hyp2 M Sig ρ fH)
    (e : ℕ → H) (t : ℕ → ℝ) (het : IsEigenSystem ρ.fst e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (g : H) (hg : fH = Tpow e t ((c - 1) / 2) g) (hgR : ‖g‖ ^ 2 ≤ R)
    (lam : ℝ) (hlam : 0 < lam)
    (fl : H) (hfl : ∀ f : H, regRisk ρ lam fl ≤ regRisk ρ lam f) :
    risk ρ fl - risk ρ fH ≤ lam ^ c * ∑' n, ⟪g, e n⟫_ℝ ^ 2 ∧
      ‖fl - fH‖ ^ 2 ≤ lam ^ (c - 1) * ∑' n, ⟪g, e n⟫_ℝ ^ 2 := by sorry

end OptimalRLS.Upper
