-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_eq_B29
-- name    : LassoDantzig.Dantzig.eq_B29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:16:22.172215+00:00
-- url     : https://prove2.me/theorems/2c73c12d-a141-4a54-a74c-d36b078e887c
-- title:
--   Proof of Theorem 7.1, (B.29) — $\ell_2$ error bound under RE$(s,m,1)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, let $m\ge1$ and let $\kappa>0$ be a witness of Assumption RE$(s,m,1)$. Let $J_0$ with $|J_0|\le s$, let $\delta\in\mathbb R^M$ satisfy the cone condition $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$, let $J_1$ be a set of the $m$ largest in absolute value coordinates of $\delta$ outside $J_0$, $J_{01}=J_0\cup J_1$, let $r\ge0$, and suppose (B.25) holds: $\frac1n|X\delta|_2^2\le4r\sqrt s\,|\delta_{J_0}|_2$. Then
--
--   $$
--   \frac1n|X\delta|_2^2\le4r\sqrt s\,|\delta_{J_{01}}|_2,\qquad |\delta_{J_{01}}|_2\le\frac{4r\sqrt s}{\kappa^2},
--   $$
--
--   and
--
--   $$
--   |\delta|_2^2\le16\Big(1+\sqrt{\frac sm}\Big)^2\Big(\frac{r\sqrt s}{\kappa^2}\Big)^2 . \tag{B.29}
--   $$
--
--   Combined with the $\ell_1$ bound (7.4) through an interpolation inequality, this gives the $\ell_p$ rates (7.6).
--
--   **Formalization Note** Deterministic form of the step the paper performs on $\mathcal B$ for $\delta=\hat\beta_D-\beta^*$, $J_0=J(\beta^*)$, with $c_0=1$ substituted in (B.29). $\kappa$ is any positive witness of RE$(s,m,1)$; $\kappa(s,m,1)$ is one.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 28, proof of Theorem 7.1, the two displays before (B.29) and Eq. (B.29)

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.29) and the two displays before it (p. 28), deterministic form.
Let `κ > 0` be a witness of RE(s, m, 1), `m ≥ 1`, `|J₀| ≤ s`, `δ` satisfy the cone condition
(4.1) at `J₀` with `c₀ = 1`, `J₁` be a set of the `m` largest `|δⱼ|` outside `J₀`, `r ≥ 0`, and
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (the conclusion of (B.25)). Then
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀₁}|_2`, `|δ_{J₀₁}|_2 ≤ 4r√s/κ²`, and
`|δ|_2² ≤ 16 (1 + √(s/m))² (r√s/κ²)²`. -/
theorem eq_B29 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (hRE : REm X s m 1 κ)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (hJ1 : IsTopBlock δ J0 J1 m) (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ (J0 ∪ J1) ∧
    l2On δ (J0 ∪ J1) ≤ 4 * r * Real.sqrt s / κ ^ 2 ∧
    ∑ j, δ j ^ 2 ≤
      16 * (1 + Real.sqrt ((s : ℝ) / m)) ^ 2 * (r * Real.sqrt s / κ ^ 2) ^ 2 := by sorry

end LassoDantzig.Dantzig
