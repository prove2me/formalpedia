-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_theorem_6_1
-- name    : LassoDantzig.Oracle.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:11:14.382791+00:00
-- url     : https://prove2.me/theorems/be797308-46d9-4a7f-93b1-53b79ba22086
-- title:
--   Theorem 6.1 — sparsity oracle inequality for the Lasso prediction loss
-- statement:
--   Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma^2>0$, and observe $y=f+W$, where $f\in\mathbb R^n$ is an **arbitrary** target and $X\in\mathbb R^{n\times M}$ a design with nonzero column norms $\|f_j\|_n$. Fix $\varepsilon>0$ and integers $n\ge1$, $M\ge2$, $1\le s\le M$, and let Assumption RE$(s,(3+4/\varepsilon)f_{\max}/f_{\min})$ hold with constant $\kappa>0$. Let $r=A\sigma\sqrt{\log M/n}$ for some $A>2\sqrt2$. Then there is an event of probability at least $1-M^{1-A^2/8}$ on which every Lasso solution $\hat\beta_L$ of (2.1), with $\hat f_L=X\hat\beta_L$, satisfies, for every $\beta\in\mathbb R^M$ with $\mathcal M(\beta)\le s$,
--   $$\|\hat f_L-f\|_n^2\le(1+\varepsilon)\Big\{\|f_\beta-f\|_n^2+C(\varepsilon)\,\frac{f_{\max}^2A^2\sigma^2}{\kappa^2}\,\frac{\mathcal M(\beta)\log M}{n}\Big\},\qquad C(\varepsilon)=\frac{4(2+\varepsilon)^2}{\varepsilon(1+\varepsilon)} .$$
--   Equivalently, $\|\hat f_L-f\|_n^2$ is at most $(1+\varepsilon)$ times the infimum of the braces over all $\beta$ with $\mathcal M(\beta)\le s$: the Lasso predicts almost as well as the best $s$-sparse linear combination of the dictionary, up to a remainder of order $\mathcal M(\beta)\log M/n$.
--
--   **Formalization Note** The paper writes "$C(\varepsilon)>0$ is a constant depending only on $\varepsilon$"; the proof (p. 26, $b=1+2/\varepsilon$) yields $C(\varepsilon)=4(2+\varepsilon)^2/(\varepsilon(1+\varepsilon))$, which is stated explicitly (a strengthening that implies the printed statement). The infimum is replaced by "for every $\beta$ with $\mathcal M(\beta)\le s$" on one event chosen before $\beta$ and the minimiser; this is equivalent since the index set is nonempty ($\beta=0$) and the braces are nonnegative. $\kappa$ is any witness of RE (the paper's $\kappa(s,c_0)$ is the largest one). "With probability at least" is a measurable event $E$ with $P(E)\ge1-M^{1-A^2/8}$. Dictionary functions enter only through $X$ and $f$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 13, Theorem 6.1, Eq. (6.1); constant C(ε) from the proof, p. 26

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Theorem 6.1** (p. 13), with the constant the proof (p. 26) yields,
`C(ε) = 4(2 + ε)²/(ε(1 + ε))`. Let `W_i` be independent `N(0, σ²)`, `σ² > 0`; fix `ε > 0`,
`n ≥ 1`, `M ≥ 2`, `1 ≤ s ≤ M`, and let RE(s, (3 + 4/ε) f_max/f_min) hold with witness `κ > 0`.
Let `r = Aσ√(log M / n)` with `A > 2√2`. With probability at least `1 − M^{1−A²/8}`, every Lasso
solution `β̂_L` of (2.1) with data `y = f + W` satisfies, for every `β` with `𝓜(β) ≤ s`,
`‖f̂_L − f‖_n² ≤ (1 + ε) (‖f_β − f‖_n² + C(ε) f_max² A² σ² / κ² · 𝓜(β) log M / n)`.
The target `f` is arbitrary. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (ε : ℝ) (hε : 0 < ε) (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ, sparsity β ≤ s →
          empSq (fun i => X.mulVec βhat i - f i) ≤
            (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
              4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * A ^ 2 * σ ^ 2 / κ ^ 2 *
                ((sparsity β : ℝ) * Real.log M / n)) := by sorry

end LassoDantzig.Oracle
