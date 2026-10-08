-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_3_N
-- name    : OptimalRLS.Upper.proposition_3_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:26:21.541823+00:00
-- url     : https://prove2.me/theorems/66dea06e-322b-4e25-89e6-f6cf3be242b3
-- title:
--   Proposition 3, p. 19 — for ρ ∈ P(b, c), b < +∞: N(λ) ≤ (b/(b−1)) β^(1/b) λ^(−1/b) (constant corrected)
-- statement:
--   Let $1<b<+\infty$, $1\le c\le2$ and $\rho\in\mathcal P(b,c)$, with the eigenvalues $t_1\ge t_2\ge\cdots>0$ of $T$ satisfying $\alpha\le n^bt_n\le\beta$ for all $n\ge1$. Then for every $\lambda>0$ the effective dimension satisfies
--   $$\mathcal N(\lambda)=\sum_{n\ge1}\frac{t_n}{t_n+\lambda}\le\frac b{b-1}\,\beta^{1/b}\,\lambda^{-1/b}.$$
--
--   This is the complexity part of the rate of Theorem 1: with $\lambda=\lambda_\ell$, the term $\Sigma^2\mathcal N(\lambda)/\ell$ of Theorem 4 balances the approximation term $\lambda^c$.
--
--   **Formalization Note** The paper prints $\mathcal N(\lambda)\le\frac{\beta b}{b-1}\lambda^{-1/b}$. Its proof bounds $\mathcal N(\lambda)\le\lambda^{-1/b}\int_0^\infty\frac{\beta}{\beta+\tau^b}d\tau$ and then claims this integral is at most $\frac b{b-1}$; in fact $\int_0^\infty\frac\beta{\beta+\tau^b}d\tau=\beta^{1/b}\int_0^\infty\frac{du}{1+u^b}\le\beta^{1/b}\frac b{b-1}$. The printed bound fails for small $\beta$ (for $b=2$, $t_n=\beta/n^2$, $\beta=0.1$: $\mathcal N(\lambda)\approx0.50\lambda^{-1/2}>0.2\lambda^{-1/2}$ as $\lambda\to0$), and agrees with the corrected one when $\beta\ge1$. The corrected constant $\beta^{1/b}$ is stated. The clauses of Definition 1 are hypotheses, as in the bounds on $\mathcal A$ and $\mathcal B$; the eigen-system is indexed from $0$, so (17) reads $\alpha\le(n+1)^bt_n\le\beta$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 3 (N, b < +∞), pp. 18–19 and its proof, p. 19

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Proposition 3, bound on `N(λ)` for `b < +∞`** (p. 19), with the constant corrected to
`β^{1/b}`. Let `ρ ∈ P(b, c)` with `1 < b < +∞`, `1 ≤ c ≤ 2` (clauses of Definition 1 unpacked). For
every `λ > 0`, `N(λ) = ∑_n t_n/(t_n + λ) ≤ (b/(b−1)) β^{1/b} λ^{−1/b}`. -/
theorem proposition_3_N
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
    (lam : ℝ) (hlam : 0 < lam) :
    effDim t lam ≤ b / (b - 1) * β ^ (1 / b) * lam ^ (-(1 / b)) := by sorry

end OptimalRLS.Upper
