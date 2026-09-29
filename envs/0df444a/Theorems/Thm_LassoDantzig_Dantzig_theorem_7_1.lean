-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_theorem_7_1
-- name    : LassoDantzig.Dantzig.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:17:11.858039+00:00
-- url     : https://prove2.me/theorems/291cd143-0243-4981-bec0-9386696e5599
-- title:
--   Theorem 7.1 — $\ell_1$, $\ell_p$ and prediction error bounds for the Dantzig selector
-- statement:
--   Consider the linear regression model
--
--   $$
--   y=X\beta^*+w,
--   $$
--
--   with a deterministic design $X\in\mathbb R^{n\times M}$, $n\ge1$, $M\ge2$, whose Gram matrix $X^TX/n$ has all diagonal elements equal to 1, a vector $\beta^*\in\mathbb R^M$ with $\mathcal M(\beta^*)=|\{j:\beta^*_j\neq0\}|\le s$ where $1\le s\le M$, and noise $w=(W_1,\dots,W_n)$ with independent $\mathcal N(0,\sigma^2)$ coordinates, $\sigma>0$. Let Assumption RE$(s,1)$ hold with constant $\kappa=\kappa(s,1)>0$. Consider the Dantzig selector
--
--   $$
--   \hat\beta_D\in\arg\min_{\beta\in\Lambda}|\beta|_1,\qquad\Lambda=\Big\{\beta\in\mathbb R^M:\Big|\frac1nX^T(y-X\beta)\Big|_\infty\le r\Big\},\qquad r=A\sigma\sqrt{\frac{\log M}{n}},
--   $$
--
--   with $A>\sqrt2$. Then there is an event of probability at least $1-M^{1-A^2/2}$ on which every such $\hat\beta_D$ satisfies
--
--   $$
--   |\hat\beta_D-\beta^*|_1\le\frac{8A}{\kappa^2(s,1)}\,\sigma s\sqrt{\frac{\log M}{n}}, \tag{7.4}
--   $$
--
--   $$
--   |X(\hat\beta_D-\beta^*)|_2^2\le\frac{16A^2}{\kappa^2(s,1)}\,\sigma^2s\log M, \tag{7.5}
--   $$
--
--   and, on the same event, whenever $s\le m$, $s+m\le M$ and Assumption RE$(s,m,1)$ holds, simultaneously for all $1<p\le2$,
--
--   $$
--   |\hat\beta_D-\beta^*|_p^p\le2^{p-1}\,8\Big\{1+\sqrt{\frac sm}\Big\}^{2(p-1)}s\Big(\frac{A\sigma}{\kappa^2(s,m,1)}\sqrt{\frac{\log M}{n}}\Big)^p. \tag{7.6}
--   $$
--
--   Here $|\delta|_p^p=\sum_j|\delta_j|^p$ and $|v|_2^2=\sum_iv_i^2$ (no normalisation by $n$). The theorem gives the rates of convergence of the Dantzig selector for estimation of a sparse parameter in every $\ell_p$ norm, $1\le p\le2$, and for prediction, under the restricted eigenvalue assumption.
--
--   **Formalization Note** The dictionary of the paper enters only through $X$; the model is `y ω = X β* + W(ω)`. RE$(s,1)$ and RE$(s,m,1)$ are stated through positive witnesses $\kappa$ and $\kappa'$ (any number with the defining property; $\kappa(s,1)$ and $\kappa(s,m,1)$ are the largest), which is equivalent to the paper's statement because the bounds decrease in $\kappa$. The two constants are kept separate: $\kappa$ in (7.4)–(7.5), $\kappa'$ in (7.6). "With the same probability as above" is rendered as the same event $E$, which depends on neither $\hat\beta_D$, $m$, $\kappa'$ nor $p$; the conclusions hold for every minimiser in (7.3). The paper's condition $s\le M/2$ for RE$(s,m,1)$ follows from $s\le m$, $s+m\le M$. $\log$ is the natural logarithm; real powers are `Real.rpow`.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 16, Theorem 7.1, Eqs. (7.4)–(7.6); proof in Appendix B, pp. 27–28

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Dantzig

/-- **Theorem 7.1**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, p. 16. Linear model (7.1)
`y = Xβ* + w` with `n ≥ 1`, `M ≥ 2`, all diagonal elements of `XᵀX/n` equal to 1,
`𝓜(β*) ≤ s`, `1 ≤ s ≤ M`, independent `N(0, σ²)` noise, `σ > 0`, and a positive witness `κ`
of RE(s, 1). Let `r = Aσ√(log M / n)` with `A > √2`. Then there is an event of probability at
least `1 − M^{1 − A²/2}` on which every Dantzig selector `β̂_D` (7.3) satisfies
(7.4) `|β̂_D − β*|_1 ≤ (8A/κ²) σ s √(log M / n)` and
(7.5) `|X(β̂_D − β*)|_2² ≤ (16A²/κ²) σ² s log M`, and, for every `m` with `s ≤ m`,
`s + m ≤ M` and every positive witness `κ'` of RE(s, m, 1), simultaneously for all
`1 < p ≤ 2`,
(7.6) `|β̂_D − β*|_p^p ≤ 2^{p−1} 8 {1 + √(s/m)}^{2(p−1)} s ((Aσ/κ'²) √(log M / n))^p`. -/
theorem theorem_7_1 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (βstar : Fin M → ℝ) (s : ℕ) (hs : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 2) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βD : Fin M → ℝ,
        IsDantzig X (fun i => X.mulVec βstar i + W i ω) r βD →
        (∑ j, |βD j - βstar j| ≤ 8 * A / κ ^ 2 * σ * s * Real.sqrt (Real.log M / n)) ∧
        (∑ i, X.mulVec (βD - βstar) i ^ 2 ≤ 16 * A ^ 2 / κ ^ 2 * σ ^ 2 * s * Real.log M) ∧
        (∀ (m : ℕ) (κ' : ℝ), s ≤ m → s + m ≤ M → 0 < κ' → REm X s m 1 κ' →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            ∑ j, |βD j - βstar j| ^ p ≤
              (2 : ℝ) ^ (p - 1) * 8 * (1 + Real.sqrt ((s : ℝ) / m)) ^ (2 * (p - 1)) * s *
                (A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n)) ^ p) := by sorry

end LassoDantzig.Dantzig
