-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_eq_B25
-- name    : LassoDantzig.Dantzig.eq_B25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:13:43.502561+00:00
-- url     : https://prove2.me/theorems/08d053ee-961f-47ed-ae01-e11a88536d93
-- title:
--   Proof of Theorem 7.1, (B.25) — on $\mathcal B$: $\frac1n|X\delta|_2^2\le 4r\sqrt s\,|\delta_{J_0}|_2$
-- statement:
--   Consider the linear model $y=X\beta^*+w$ with $X\in\mathbb R^{n\times M}$, $n\ge1$, all diagonal elements of $X^TX/n$ equal to 1, and $\mathcal M(\beta^*)\le s$. Suppose the noise vector $w$ lies in the event $\mathcal B$, i.e. $|\frac1n\sum_iX_{ij}w_i|\le r$ for every $j$, and let $\hat\beta_D$ be a Dantzig selector (7.3), i.e. $\hat\beta_D\in\arg\min_{\beta\in\Lambda}|\beta|_1$ with $\Lambda=\{\beta:|\frac1nX^T(y-X\beta)|_\infty\le r\}$. Set $\delta=\hat\beta_D-\beta^*$ and $J_0=J(\beta^*)$. Then
--
--   1. $\beta^*\in\Lambda$;
--   2. $\frac1n|X^TX\delta|_\infty\le2r$;
--   3. $\delta$ satisfies the cone condition (4.1) with $c_0=1$: $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$;
--   4. the prediction error is controlled by the error on the support:
--   $$
--   \frac1n|X\delta|_2^2\le4r\sqrt s\,|\delta_{J_0}|_2 . \tag{B.25}
--   $$
--
--   Combined with the restricted eigenvalue assumption this gives all the rates of Theorem 7.1.
--
--   **Formalization Note** The event $\mathcal B$ is written with the weights $\|f_j\|_n$ of the general definition; under the unit-diagonal hypothesis they equal 1. The statement is deterministic: it holds for every realised noise vector in $\mathcal B$ and every Dantzig selector.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, proof of Theorem 7.1, Eq. (B.25) and the sentence before it

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.25) (p. 27). Linear model `y = Xβ* + w` with unit diagonal
`XᵀX/n`, `𝓜(β*) ≤ s`, a realised noise vector `w` in the event `ℬ`, and a Dantzig selector
`β̂_D` (7.3). With `δ = β̂_D − β*` and `J₀ = J(β*)`: `β* ∈ Λ`;
(i) `(1/n)|XᵀXδ|_∞ ≤ 2r`; (ii) the cone condition (4.1) holds with `c₀ = 1`; and
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2`. -/
theorem eq_B25 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (βstar : Fin M → ℝ) (s : ℕ) (hsparse : sparsity βstar ≤ s)
    (w : Fin n → ℝ) (r : ℝ) (hB : NoiseEvent X r w)
    (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => X.mulVec βstar i + w i) r βD) :
    InLambda X (fun i => X.mulVec βstar i + w i) r βstar ∧
    (∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βD - βstar) i| ≤ 2 * r) ∧
    ConeCond 1 (supp βstar) (βD - βstar) ∧
    (1 / (n : ℝ)) * ∑ i, X.mulVec (βD - βstar) i ^ 2 ≤
      4 * r * Real.sqrt s * l2On (βD - βstar) (supp βstar) := by sorry

end LassoDantzig.Dantzig
