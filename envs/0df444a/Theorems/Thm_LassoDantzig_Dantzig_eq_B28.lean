-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_eq_B28
-- name    : LassoDantzig.Dantzig.eq_B28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:15:52.621719+00:00
-- url     : https://prove2.me/theorems/7caf3d7b-ab1f-4b66-9f97-2ecd857becbc
-- title:
--   Proof of Theorem 7.1, (B.28) — $|\delta|_2\le(1+c_0\sqrt{s/m})\,|\delta_{J_{01}}|_2$ on the cone
-- statement:
--   Let $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$, let $m\ge1$, let $\delta\in\mathbb R^M$, and let $J_1$ be a set of the $m$ largest in absolute value coordinates of $\delta$ outside $J_0$ (so $J_1\subseteq J_0^c$, $|J_1|=m$, and no coordinate of $\delta$ in $J_0^c\setminus J_1$ exceeds in absolute value any coordinate in $J_1$); put $J_{01}=J_0\cup J_1$. Then
--
--   $$
--   |\delta_{J_{01}^c}|_2^2\le\frac1m|\delta_{J_0^c}|_1^2 .
--   $$
--
--   If moreover $c_0>0$ and $\delta$ satisfies the cone condition (4.1), $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$, then
--
--   $$
--   |\delta_{J_{01}^c}|_2\le\frac{c_0|\delta_{J_0}|_1}{\sqrt m}\le c_0|\delta_{J_0}|_2\sqrt{\frac sm}\le c_0|\delta_{J_{01}}|_2\sqrt{\frac sm},
--   \qquad
--   |\delta|_2\le\Big(1+c_0\sqrt{\frac sm}\Big)|\delta_{J_{01}}|_2 . \tag{B.28}
--   $$
--
--   This reduces the full $\ell_2$ error to the error on $J_{01}$, which Assumption RE$(s,m,c_0)$ controls.
--
--   **Formalization Note** The paper states the displays "on $\mathcal B$" for $\delta=\hat\beta_D-\beta^*$ with $c_0=1$; they are deterministic consequences of the cone condition and are stated here for general $c_0>0$ and every admissible choice of $J_1$ under ties. The paper's range $s\le m$, $s+m\le M$ is not needed.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, proof of Theorem 7.1, the two displays before (B.28) and Eq. (B.28)

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.28) and the two displays before it (p. 27). Let `|J₀| ≤ s`,
`m ≥ 1`, and let `J₁` be a set of the `m` largest `|δⱼ|` outside `J₀`, `J₀₁ = J₀ ∪ J₁`. Then
`|δ_{J₀₁ᶜ}|_2² ≤ (1/m)|δ_{J₀ᶜ}|_1²`; if moreover `c₀ > 0` and `δ` satisfies the cone condition
(4.1), then `|δ_{J₀₁ᶜ}|_2 ≤ c₀|δ_{J₀}|_1/√m ≤ c₀|δ_{J₀}|_2 √(s/m) ≤ c₀|δ_{J₀₁}|_2 √(s/m)` and
`|δ|_2 ≤ (1 + c₀√(s/m)) |δ_{J₀₁}|_2`. -/
theorem eq_B28 {M : ℕ} (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ)
    (hJ1 : IsTopBlock δ J0 J1 m) (hcone : ConeCond c0 J0 δ) :
    l2On δ (J0 ∪ J1)ᶜ ^ 2 ≤ (1 / (m : ℝ)) * l1On δ J0ᶜ ^ 2 ∧
    l2On δ (J0 ∪ J1)ᶜ ≤ c0 * l1On δ J0 / Real.sqrt m ∧
    c0 * l1On δ J0 / Real.sqrt m ≤ c0 * l2On δ J0 * Real.sqrt ((s : ℝ) / m) ∧
    c0 * l2On δ J0 * Real.sqrt ((s : ℝ) / m) ≤ c0 * l2On δ (J0 ∪ J1) * Real.sqrt ((s : ℝ) / m) ∧
    Real.sqrt (∑ j, δ j ^ 2) ≤ (1 + c0 * Real.sqrt ((s : ℝ) / m)) * l2On δ (J0 ∪ J1) := by sorry

end LassoDantzig.Dantzig
