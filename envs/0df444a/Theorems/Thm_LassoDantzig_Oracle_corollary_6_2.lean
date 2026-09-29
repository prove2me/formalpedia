-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_corollary_6_2
-- name    : LassoDantzig.Oracle.corollary_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:11:46.657977+00:00
-- url     : https://prove2.me/theorems/09e73349-a0ff-49fd-a5df-48198ca86326
-- title:
--   Corollary 6.2 — oracle inequality for the Lasso over $\bar\Lambda_{s,\gamma,\varepsilon}$ without a global RE assumption
-- statement:
--   Let $W_i$, $s$ and the Lasso be as in Theorem 6.1 ($W_1,\dots,W_n$ independent $\mathcal N(0,\sigma^2)$ with $\sigma>0$, $n\ge1$, $M\ge2$, $1\le s\le M$, nonzero column norms, arbitrary $f$, $r=A\sigma\sqrt{\log M/n}$ with $A>2\sqrt2$), but without the RE assumption. For $\gamma>0$ and $c_0>0$ let
--   $$\mathcal J_{s,\gamma,c_0}=\Big\{J_0:|J_0|\le s,\ \min_{\delta\ne0,\ |\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1}\frac{|X\delta|_2}{\sqrt n\,|\delta_{J_0}|_2}\ge\gamma\Big\},\qquad \Lambda_{s,\gamma,c_0}=\{\beta:J(\beta)\in\mathcal J_{s,\gamma,c_0}\},$$
--   and $\bar\Lambda_{s,\gamma,\varepsilon}=\{\beta\in\Lambda_{s,\gamma,(3+4/\varepsilon)f_{\max}/f_{\min}}:\mathcal M(\beta)\le s\}$. Then for all $\varepsilon>0$ and $\gamma>0$ there is an event of probability at least $1-M^{1-A^2/8}$ on which every Lasso solution $\hat\beta_L$ satisfies, for every $\beta\in\bar\Lambda_{s,\gamma,\varepsilon}$,
--   $$\|\hat f_L-f\|_n^2\le(1+\varepsilon)\Big\{\|f_\beta-f\|_n^2+C(\varepsilon)\,\frac{f_{\max}^2A^2\sigma^2}{\gamma^2}\,\frac{\mathcal M(\beta)\log M}{n}\Big\},\qquad C(\varepsilon)=\frac{4(2+\varepsilon)^2}{\varepsilon(1+\varepsilon)} .$$
--
--   The corollary requires the restricted eigenvalue inequality only at the support of the competitor $\beta$, which removes the pathologies of a global RE assumption discussed at the end of Section 4.
--
--   **Formalization Note** $C(\varepsilon)$ is the explicit constant of Theorem 6.1 (the paper writes "the same $C(\varepsilon)$"). The minimum in $\mathcal J_{s,\gamma,c_0}$ is encoded as "for every $\delta\neq0$ in the cone, $\gamma\sqrt n|\delta_{J_0}|_2\le|X\delta|_2$"; for $J_0=\emptyset$ the cone contains only $0$ and the condition holds, matching the convention $\min\emptyset=+\infty$. The infimum over $\bar\Lambda$ is replaced by "for every $\beta\in\bar\Lambda$", as in Theorem 6.1.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 13, Corollary 6.2 (with J_{s,γ,c0} and Λ_{s,γ,c0} defined just above it)

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Corollary 6.2** (p. 13), with the explicit `C(ε) = 4(2 + ε)²/(ε(1 + ε))` of Theorem 6.1.
Same noise, `s` and Lasso as in Theorem 6.1, but no RE assumption. For all `n ≥ 1`, `ε > 0` and
`γ > 0`, with probability at least `1 − M^{1−A²/8}`, every Lasso solution `β̂_L` satisfies, for every
`β ∈ Λ̄_{s,γ,ε} = {β ∈ Λ_{s,γ,(3+4/ε)f_max/f_min} : 𝓜(β) ≤ s}`,
`‖f̂_L − f‖_n² ≤ (1 + ε) (‖f_β − f‖_n² + C(ε) f_max² A² σ² / γ² · 𝓜(β) log M / n)`. -/
theorem corollary_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (A : ℝ) (hA : 2 * Real.sqrt 2 < A)
    (ε : ℝ) (hε : 0 < ε) (γ : ℝ) (hγ : 0 < γ) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β ∈ LambdaSet X s γ ((3 + 4 / ε) * fmax X / fmin X), sparsity β ≤ s →
          empSq (fun i => X.mulVec βhat i - f i) ≤
            (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
              4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * A ^ 2 * σ ^ 2 / γ ^ 2 *
                ((sparsity β : ℝ) * Real.log M / n)) := by sorry

end LassoDantzig.Oracle
