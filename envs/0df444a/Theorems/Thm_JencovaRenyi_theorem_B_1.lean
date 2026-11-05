-- Prove2me | Theorems.Thm_JencovaRenyi_theorem_B_1
-- name    : JencovaRenyi.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:22.429517+00:00
-- url     : https://prove2.me/theorems/3686920f-6762-4221-8474-cfed4188f491
-- title:
--   Theorem B.1 — abstract Riesz–Thorin: $\|Tx\|_\theta\le M_0^{1-\theta}M_1^\theta\|x\|_\theta$
-- statement:
--   Let $(X_0,X_1)$ and $(Y_0,Y_1)$ be compatible pairs ($X_0$ continuously embedded in $X_1$, $Y_0$ in $Y_1$) and let $T : X_1\to Y_1$ be a bounded linear operator with $T(X_0)\subseteq Y_0$. If
--   $$
--   \|Tx\|_{Y_1}\le M_1\|x\|_{X_1}\ (x\in X_1),\qquad \|Tx_0\|_{Y_0}\le M_0\|x_0\|_{X_0}\ (x_0\in X_0),
--   $$
--   then for $\theta\in(0,1)$ and every $x\in C_\theta(X_0,X_1)$,
--   $$
--   \|Tx\|_\theta\le M_0^{1-\theta}M_1^{\theta}\|x\|_\theta .
--   $$
--   This is the exactness of the complex interpolation functor; the paper uses it to interpolate the endpoint contractions of $\Phi$ (Proposition 3.12).
--
--   Differences from the source:
--   - generalization: $(X_0,X_1)$, $(Y_0,Y_1)$ compatible Banach pairs → normed spaces $X_1, Y_1$ with subspaces given by gauges satisfying `IsCompatibleGauge`; completeness not assumed; reason: the interpolation estimate does not use completeness; Banach pairs are a special case.
--   - encoding: $X_0$, $Y_0$ with their norms; $x\in C_\theta(X_0,X_1)$; $M_0, M_1$ → gauges $n_0, m_0 : \cdot\to[0,\infty]$ ($X_0 = \{n_0<\infty\}$); the hypothesis `interpNorm n₀ θ x < ⊤`; $M_0,M_1\in\mathbb R_{\ge0}$; $T(X_0)\subseteq Y_0$ is carried by $m_0(Tx)\le M_0 n_0(x)$ for $n_0(x)<\infty$; reason: Lean convention for subspaces with their own norm; the same operators and the same conclusion.
--   - reading: $\|Tx_0\|_{X_0}\le M_0\|x_0\|_{X_0}$ as printed → `m₀ (T x) ≤ M₀ * n₀ x`, the $Y_0$ norm on the left; reason: $Tx_0$ lies in $Y_0$, where the $X_0$ norm is not defined, so the printed subscript can only mean $Y_0$.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Theorem B.1, p.23

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_interpNorm
import Definitions.Def_JencovaRenyi_IsCompatibleGauge
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Theorem B.1 of Jenčová, arXiv:1609.08462v4, Appendix B, p.23 (abstract Riesz–Thorin). Let
`(X₀, X₁)` and `(Y₀, Y₁)` be compatible pairs (`X₀ = {n₀ < ∞} ⊆ X₁`, `Y₀ = {m₀ < ∞} ⊆ Y₁`) and
let `T : X₁ → Y₁` be a bounded linear operator with `T(X₀) ⊆ Y₀`. If `‖Tx‖_{Y₁} ≤ M₁ ‖x‖_{X₁}`
for `x ∈ X₁` and `‖Tx₀‖_{Y₀} ≤ M₀ ‖x₀‖_{X₀}` for `x₀ ∈ X₀`, then for `θ ∈ (0, 1)` and
`x ∈ C_θ(X₀, X₁)`, `‖Tx‖_θ ≤ M₀^{1−θ} M₁^θ ‖x‖_θ`.

Completeness of the four spaces is not assumed. -/
theorem theorem_B_1 {X₁ Y₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    (n₀ : X₁ → ℝ≥0∞) (m₀ : Y₁ → ℝ≥0∞) (hn₀ : IsCompatibleGauge n₀) (hm₀ : IsCompatibleGauge m₀)
    (T : X₁ →L[ℂ] Y₁) (M₀ M₁ : NNReal)
    (hT₁ : ∀ x : X₁, (‖T x‖₊ : ℝ≥0∞) ≤ M₁ * ‖x‖₊)
    (hT₀ : ∀ x : X₁, n₀ x < ⊤ → m₀ (T x) ≤ M₀ * n₀ x)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (x : X₁) (hx : interpNorm n₀ θ x < ⊤) :
    interpNorm m₀ θ (T x) ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * interpNorm n₀ θ x := by sorry

end JencovaRenyi
