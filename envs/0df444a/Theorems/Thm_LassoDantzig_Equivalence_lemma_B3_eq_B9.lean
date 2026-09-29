-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_lemma_B3_eq_B9
-- name    : LassoDantzig.Equivalence.lemma_B3_eq_B9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:00:32.460597+00:00
-- url     : https://prove2.me/theorems/00f6c214-e583-4851-9c82-862719f8e950
-- title:
--   Lemma B.3, (B.9) — the Dantzig error lies in the cone $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$
-- statement:
--   Let $n\ge1$, $X\in\mathbb R^{n\times M}$, $y\in\mathbb R^n$ and $r>0$. Let $\beta\in\mathbb R^M$ satisfy the Dantzig constraint
--   $$
--   \Big|\frac1n\sum_{i=1}^nX_{ij}\big(y_i-(X\beta)_i\big)\Big|\le r\|f_j\|_n\qquad(j=1,\dots,M),
--   $$
--   and let $\hat\beta_D$ be a Dantzig selector (2.4). Set $\delta=\hat\beta_D-\beta$ and $J_0=J(\beta)=\{j:\beta_j\ne0\}$. Then
--   $$
--   |\delta_{J_0^c}|_1\le|\delta_{J_0}|_1 .
--   $$
--
--   Applied with $\beta=\hat\beta_L$ (which is feasible by (2.3)) this puts the difference of the two estimators in the cone of Assumption RE$(s,1)$ with $J_0=J(\hat\beta_L)$; this is (B.12) in the proof of Theorem 5.1.
--
--   **Formalization Note** Deterministic: it holds for every feasible $\beta$ and every minimiser $\hat\beta_D$ of the Dantzig program.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 23, Lemma B.3, Eq. (B.9)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- Lemma B.3, (B.9): if `β` satisfies the Dantzig constraint and `β̂_D` is a Dantzig selector,
then with `δ = β̂_D − β` and `J₀ = J(β)`, `|δ_{J₀ᶜ}|_1 ≤ |δ_{J₀}|_1`. -/
theorem lemma_B3_eq_B9 {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (β βD : Fin M → ℝ) (hβ : DantzigFeasible X y r β) (hD : IsDantzig X y r βD) :
    l1On (βD - β) (supp β)ᶜ ≤ l1On (βD - β) (supp β) := by sorry

end LassoDantzig.Equivalence
