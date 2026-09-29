-- Prove2me | Theorems.Thm_LesHouchesWidth_jacobian_fourth_moment
-- name    : LesHouchesWidth.jacobian_fourth_moment
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T22:20:46.775992+00:00
-- url     : https://prove2.me/theorems/c6503fc0-25df-415e-92db-53cb51d9071d
-- title:
--   Section 5.5: fourth moment of the Jacobian, $\exp(5\sum_\ell 1/n_\ell+O(L/n^2))$ (case $\mu_4=3$)
-- statement:
--   Let $\mu$ satisfy the standing assumptions of Section 5.3 and in addition $\int t^4\,d\mu(t)=3$. Then there are constants $c>0$ and $C$, depending only on $\mu$, such that for every depth $L\ge1$, all widths $n_0,\dots,n_{L+1}\ge1$, every input $x\neq0$ and all $p,q$,
--   $$\mathbb E\Big[\Big(\frac{\partial z^{(L+1)}_q}{\partial x_p}\Big)^4\Big]=\frac{c}{n_0^2}\exp\Big(5\sum_{\ell=1}^{L}\frac1{n_\ell}+e\Big)\qquad\text{with}\qquad |e|\le C\,\frac{L}{m^2}$$
--   for every integer $m\ge1$ with $m\le n_\ell$ for all $1\le\ell\le L$ (in particular for $m=\min_{1\le\ell\le L}n_\ell$).
--
--   This is the statement that the fluctuations of the Jacobian grow like $e^{\beta}$ with $\beta=5\sum_\ell 1/n_\ell\approx5L/n$.
--
--   **Formalization Note** The lectures state this for general $\mu$ with finite moments. An informal computation suggests that for $\int t^4d\mu\neq3$ an additional term of order $(\int t^4 d\mu-3)(1/n_1+1/n_L)$ appears in the exponent, which is not $O(L/n^2)$. The hypothesis $\int t^4d\mu=3$ (satisfied for Gaussian weights) is added for that reason and should be reviewed.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), pp. 41–43, Section 5.5 (first display of 5.5 and Section 5.5.2).

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem jacobian_fourth_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1) (hμ_four : ∫ t, t ^ 4 ∂μ = 3) :
    ∃ c C : ℝ, 0 < c ∧
      ∀ L : ℕ, 1 ≤ L → ∀ n : ℕ → ℕ, (∀ ℓ ≤ L + 1, 1 ≤ n ℓ) →
      ∀ x : Fin (n 0) → ℝ, x ≠ 0 → ∀ (p : Fin (n 0)) (q : Fin (n (L + 1))),
        ∃ e : ℝ,
          ∫ ω, (jacobianEntry ω x p q) ^ 4 ∂(weightLaw n L μ) =
            c / (n 0 : ℝ) ^ 2 * Real.exp (5 * ∑ ℓ ∈ Finset.Icc 1 L, 1 / (n ℓ : ℝ) + e) ∧
          ∀ m : ℕ, 1 ≤ m → (∀ ℓ ∈ Finset.Icc 1 L, m ≤ n ℓ) → |e| ≤ C * L / (m : ℝ) ^ 2 := by sorry

end LesHouchesWidth
