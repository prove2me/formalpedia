-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_theorem_7_2
-- name    : LassoDantzig.Lasso.theorem_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:22:05.479259+00:00
-- url     : https://prove2.me/theorems/efe91fce-8cbe-4016-b697-1328b6423950
-- title:
--   Theorem 7.2 — $\ell_1$, prediction, sparsity and $\ell_p$ bounds for the Lasso under RE$(s,3)$
-- statement:
--   Consider the linear regression model $y=X\beta^*+w$ with a deterministic design $X\in\mathbb R^{n\times M}$, $n\ge1$, $M\ge2$, and $w=(W_1,\dots,W_n)$ with independent $\mathcal N(0,\sigma^2)$ entries, $\sigma^2>0$. Assume that all diagonal entries of $X^\top X/n$ equal $1$, that $\mathcal M(\beta^*)\le s$ with $1\le s\le M$, and that Assumption RE$(s,3)$ holds with constant $\kappa=\kappa(s,3)>0$. Let $\hat\beta_L$ be the Lasso estimator (7.2) with
--   $$
--   r=A\sigma\sqrt{\frac{\log M}{n}},\qquad A>2\sqrt2 .
--   $$
--   Then, with probability at least $1-M^{1-A^2/8}$,
--   $$
--   |\hat\beta_L-\beta^*|_1\le\frac{16A}{\kappa^2(s,3)}\,\sigma s\sqrt{\frac{\log M}{n}},\qquad\text{(7.7)}
--   $$
--   $$
--   |X(\hat\beta_L-\beta^*)|_2^2\le\frac{16A^2}{\kappa^2(s,3)}\,\sigma^2s\log M,\qquad\text{(7.8)}
--   $$
--   $$
--   \mathcal M(\hat\beta_L)\le\frac{64\phi_{\max}}{\kappa^2(s,3)}\,s,\qquad\text{(7.9)}
--   $$
--   where $\phi_{\max}$ is the largest eigenvalue of $X^\top X/n$. If moreover Assumption RE$(s,m,3)$ holds (with $1\le s\le M/2$, $m\ge s$, $s+m\le M$), then on the same event, simultaneously for all $1<p\le2$,
--   $$
--   |\hat\beta_L-\beta^*|_p^p\le16\Big\{1+3\sqrt{\frac sm}\Big\}^{2(p-1)}s\left(\frac{A\sigma}{\kappa^2(s,m,3)}\sqrt{\frac{\log M}{n}}\right)^p.\qquad\text{(7.10)}
--   $$
--
--   The theorem gives, with explicit constants and an explicit failure probability, the $\ell_1$ error rate $s\sqrt{\log M/n}$, the prediction error $s\log M$ and the $\ell_p$ rates of the Lasso for an $s$-sparse coefficient vector when $M$ may be much larger than $n$, and shows that the Lasso selects at most $64\phi_{\max}s/\kappa^2$ variables.
--
--   **Formalization Note** $X$, $\beta^*$ and the noise $W_i$ on a probability space $(\Omega,\mathbb P)$ are the data; $y(\omega)=X\beta^*+W(\omega)$. The statement provides one measurable event $E$ with $\mathbb P(E)\ge1-M^{1-A^2/8}$ on which every Lasso solution (every minimiser of (7.2)) satisfies all four bounds; the event does not depend on the solution, on $m$ or on $p$. RE$(s,3)$ and RE$(s,m,3)$ enter through witnesses $\kappa,\kappa'>0$ (every witness is at most the paper's $\kappa(s,3)$, resp. $\kappa(s,m,3)$, and the bounds decrease in $\kappa$), so the statement is equivalent to the paper's. $\phi_{\max}$ is the Rayleigh supremum of $\frac1n|Xx|_2^2$ over unit vectors. $|\delta|_p^p=\sum_j|\delta_j|^p$ with real powers; $\log$ is the natural logarithm. The ranges $1\le s\le M/2$, $m\ge s$, $s+m\le M$ are those under which RE$(s,m,c_0)$ is defined (p. 7).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 16–17, Theorem 7.2, Eqs. (7.7)–(7.10)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- Theorem 7.2, pp. 16–17: ℓ1, prediction, sparsity and ℓp bounds for the Lasso. -/
theorem theorem_7_2 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 3 κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ,
        IsLasso X (fun i => X.mulVec βstar i + W i ω) r βhat →
        -- (7.7)
        l1Norm (βhat - βstar) ≤ 16 * A / κ ^ 2 * σ * s * Real.sqrt (Real.log M / n) ∧
        -- (7.8)
        ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤ 16 * A ^ 2 / κ ^ 2 * σ ^ 2 * s * Real.log M ∧
        -- (7.9)
        (sparsity βhat : ℝ) ≤ 64 * phiMax X / κ ^ 2 * s ∧
        -- (7.10), under Assumption RE(s, m, 3) with witness κ', for all 1 < p ≤ 2
        (∀ (m : ℕ) (κ' : ℝ), 2 * s ≤ M → s ≤ m → s + m ≤ M → 0 < κ' → REm X s m 3 κ' →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            ∑ j, |βhat j - βstar j| ^ p ≤
              16 * (1 + 3 * Real.sqrt ((s : ℝ) / m)) ^ (2 * (p - 1)) * s *
                (A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n)) ^ p) := by sorry

end LassoDantzig.Lasso
