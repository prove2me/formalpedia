-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_lemma_B3_eq_B9
-- name    : LassoDantzig.Dantzig.lemma_B3_eq_B9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:13:11.67129+00:00
-- url     : https://prove2.me/theorems/a3d1526f-0b26-4f18-bc3d-6dc12c025b26
-- title:
--   Lemma B.3, (B.9) — the Dantzig selector's error lies in the cone $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$, $y\in\mathbb R^n$ and $r\in\mathbb R$. Suppose $\beta\in\mathbb R^M$ satisfies the Dantzig constraint
--
--   $$
--   \Big|\frac1n D^{-1/2}X^T(y-X\beta)\Big|_\infty\le r ,\qquad D=\mathrm{diag}(\|f_1\|_n^2,\dots,\|f_M\|_n^2),
--   $$
--
--   and let $\hat\beta_D$ be a Dantzig selector, i.e. a vector of smallest $\ell_1$ norm among those satisfying this constraint. Put $\delta=\hat\beta_D-\beta$ and $J_0=J(\beta)=\{j:\beta_j\neq0\}$. Then
--
--   $$
--   |\delta_{J_0^c}|_1\le|\delta_{J_0}|_1 . \tag{B.9}
--   $$
--
--   This places the estimation error in the cone (4.1) with $c_0=1$, which is where the restricted eigenvalue assumption can be applied.
--
--   **Formalization Note** The statement is for every Dantzig selector (minimisers need not be unique). No sign condition on $r$ is needed.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 23, Lemma B.3, Eq. (B.9)

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Lemma B.3, (B.9) (p. 23): if `β` satisfies the Dantzig constraint
`|(1/n) D^{−1/2} Xᵀ(y − Xβ)|_∞ ≤ r` and `β̂_D` is a Dantzig selector (2.4), then with
`δ = β̂_D − β` and `J₀ = J(β)`, `|δ_{J₀ᶜ}|_1 ≤ |δ_{J₀}|_1`. -/
theorem lemma_B3_eq_B9 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β βD : Fin M → ℝ) (hβ : DantzigConstraint X y r β) (hD : IsDantzigSelector X y r βD) :
    l1On (βD - β) (supp β)ᶜ ≤ l1On (βD - β) (supp β) := by sorry

end LassoDantzig.Dantzig
