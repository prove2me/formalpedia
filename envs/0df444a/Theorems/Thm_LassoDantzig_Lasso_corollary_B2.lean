-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_corollary_B2
-- name    : LassoDantzig.Lasso.corollary_B2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:19:38.512102+00:00
-- url     : https://prove2.me/theorems/c6a1d138-9a01-471d-9c9c-cfbe5e000bbd
-- title:
--   Corollary B.2 — the Lasso error lies in the cone $|\delta_{J_0^c}|_1\le3|\delta_{J_0}|_1$
-- statement:
--   Let $n\ge1$, $M\ge2$, let $X\in\mathbb R^{n\times M}$ have unit column norms, $\frac1n\sum_iX_{ij}^2=1$ for all $j$, and consider the linear regression model $y=X\beta+w$ where $w$ has independent $\mathcal N(0,\sigma^2)$ entries, $\sigma>0$. Let $A>2\sqrt2$ and $r=A\sigma\sqrt{\log M/n}$. Then there is an event of probability at least $1-M^{1-A^2/8}$ on which every Lasso solution $\hat\beta_L$ of (7.2) satisfies
--   $$
--   |\delta_{J_0^c}|_1\le3|\delta_{J_0}|_1,
--   $$
--   where $J_0=J(\beta)$ is the set of non-zero coefficients of $\beta$ and $\delta=\hat\beta_L-\beta$.
--
--   This cone condition is what allows Assumption RE$(s,3)$ to be applied to the error vector $\delta$.
--
--   **Formalization Note** The event is measurable, independent of $\hat\beta_L$, and the conclusion holds for every minimiser of (7.2).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 22, Corollary B.2

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- Corollary B.2, p. 22: in the linear regression model `y = Xβ + w` with unit column norms,
with probability at least `1 − M^{1 − A²/8}`, every Lasso solution `β̂` satisfies the cone
condition `|δ_{J₀ᶜ}|_1 ≤ 3|δ_{J₀}|_1` with `J₀ = J(β)` and `δ = β̂ − β`. -/
theorem corollary_B2 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (β : Fin M → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ,
        IsLasso X (fun i => X.mulVec β i + W i ω) r βhat →
        ConeCond 3 (supp β) (βhat - β) := by sorry

end LassoDantzig.Lasso
