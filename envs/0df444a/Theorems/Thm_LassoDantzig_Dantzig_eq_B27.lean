-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_eq_B27
-- name    : LassoDantzig.Dantzig.eq_B27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:15:23.0989+00:00
-- url     : https://prove2.me/theorems/a91e37c4-d894-4c0c-9f73-7311a889d571
-- title:
--   Proof of Theorem 7.1, (B.27) — $|\delta|_1\le(1+c_0)\sqrt s\,|\delta_{J_0}|_2$ on the cone
-- statement:
--   Let $c_0>0$, $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$, and let $\delta\in\mathbb R^M$ satisfy the cone condition (4.1), $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$. Then
--
--   $$
--   |\delta|_1=|\delta_{J_0}|_1+|\delta_{J_0^c}|_1\le(1+c_0)|\delta_{J_0}|_1\le(1+c_0)\sqrt s\,|\delta_{J_0}|_2 . \tag{B.27}
--   $$
--
--   Together with the second inequality of (B.26) this yields the $\ell_1$ rate (7.4).
--
--   **Formalization Note** Each of the three relations of the chain is a separate conjunct.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, proof of Theorem 7.1, Eq. (B.27)

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.27) (p. 27): if `|J₀| ≤ s`, `c₀ > 0` and `δ` satisfies the cone
condition (4.1) `|δ_{J₀ᶜ}|_1 ≤ c₀|δ_{J₀}|_1`, then
`|δ|_1 = |δ_{J₀}|_1 + |δ_{J₀ᶜ}|_1 ≤ (1 + c₀)|δ_{J₀}|_1 ≤ (1 + c₀)√s |δ_{J₀}|_2`. -/
theorem eq_B27 {M : ℕ} (s : ℕ) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond c0 J0 δ) :
    ∑ j, |δ j| = l1On δ J0 + l1On δ J0ᶜ ∧
    l1On δ J0 + l1On δ J0ᶜ ≤ (1 + c0) * l1On δ J0 ∧
    (1 + c0) * l1On δ J0 ≤ (1 + c0) * Real.sqrt s * l2On δ J0 := by sorry

end LassoDantzig.Dantzig
