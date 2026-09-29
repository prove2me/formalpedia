-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_eq_B26
-- name    : LassoDantzig.Dantzig.eq_B26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:14:15.116551+00:00
-- url     : https://prove2.me/theorems/68c841e4-6111-4a2a-867c-e24e080e6cc7
-- title:
--   Proof of Theorem 7.1, (B.26) — prediction and support-error bounds under RE$(s,1)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, and let $\kappa>0$ be a witness of Assumption RE$(s,1)$. Let $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$, let $\delta\in\mathbb R^M$ satisfy the cone condition $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$, let $r\ge0$, and suppose that (B.25) holds:
--   $\frac1n|X\delta|_2^2\le4r\sqrt s\,|\delta_{J_0}|_2$. Then
--
--   $$
--   \frac1n|X\delta|_2^2\le\frac{16r^2s}{\kappa^2},\qquad |\delta_{J_0}|_2\le\frac{4r\sqrt s}{\kappa^2}. \tag{B.26}
--   $$
--
--   The first inequality is the prediction bound (7.5); the second feeds the $\ell_1$ bound (7.4) through (B.27).
--
--   **Formalization Note** This is the deterministic step of the proof: the paper applies it on the event $\mathcal B$ to $\delta=\hat\beta_D-\beta^*$ and $J_0=J(\beta^*)$, for which the hypotheses are supplied by (B.25). $\kappa$ is any positive witness of RE$(s,1)$ (see the definitions); $\kappa=\kappa(s,1)$ is one.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, proof of Theorem 7.1, Eq. (B.26)

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.26) (p. 27), deterministic form. If `κ > 0` is a witness of
RE(s, 1), `|J₀| ≤ s`, `δ` satisfies the cone condition (4.1) at `J₀` with `c₀ = 1`, `r ≥ 0`,
and `(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (the conclusion of (B.25)), then
`(1/n)|Xδ|_2² ≤ 16r²s/κ²` and `|δ_{J₀}|_2 ≤ 4r√s/κ²`. -/
theorem eq_B26 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s : ℕ) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
    l2On δ J0 ≤ 4 * r * Real.sqrt s / κ ^ 2 := by sorry

end LassoDantzig.Dantzig
