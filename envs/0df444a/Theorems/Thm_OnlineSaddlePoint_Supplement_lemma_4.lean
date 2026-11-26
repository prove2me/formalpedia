-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_lemma_4
-- name    : OnlineSaddlePoint.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:54:40.442294+00:00
-- url     : https://prove2.me/theorems/be0f1ca3-8e27-428a-834d-f7583fd3674e
-- title:
--   Lemma 4 — $\sum_i x_i\ln x_i$ is $\max\{|\ln\theta|,1\}$-Lipschitz in $\|\cdot\|_1$ on $\Delta_\theta$
-- statement:
--   Let $d\in\mathbb N$ and $\theta>0$, and let $R(x)=\sum_{i=1}^d x_i\ln x_i$. For all $a,b$ in the restricted simplex $\Delta_\theta=\{z\in\mathbb R^d:\|z\|_1=1,\ z_i\ge\theta\}$,
--
--   $$
--   |R(a)-R(b)|\le\max\{|\ln\theta|,\,1\}\;\|a-b\|_1 .
--   $$
--
--   The negative entropy is not Lipschitz on the whole simplex (its gradient $1+\ln x_i$ blows up at the boundary); keeping every coordinate at least $\theta$ restores a Lipschitz constant that grows only logarithmically in $1/\theta$. This is what lets Theorem 2 apply to the entropic regularizers of OMG-RFTL.
--
--   Differences from the source:
--   - encoding: $\theta\in[0,1/d]$ (display (10)) → $\theta>0$; reason: $\ln\theta$ is undefined at $\theta=0$; only that undefined case is excluded
--   - generalization: $\theta\le1/d$ → no upper bound on $\theta$; reason: for $\theta>1/d$ the set $\Delta_\theta$ is empty and the statement holds vacuously; for $\theta\le1/d$ it is the source's
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
--   - encoding: $\ln$ → `Real.log`; reason: the natural logarithm; only evaluated at positive arguments in the bound
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 4, p.16

import Mathlib
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex
import Definitions.Def_OnlineSaddlePoint_Supplement_negEntropy

namespace OnlineSaddlePoint.Supplement

/-- **Lemma 4 (Lipschitz constant of the negative entropy on `Δ_θ`).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 4, p.16: "The function `R(x) ≜ ∑_{i=1}^d x_i ln(x_i)` is `G_R`-Lipschitz
continuous with respect to `‖·‖₁` over `Δ_θ` with `G_R = max{|ln(θ)|, 1}`."

**Formalization Note.** `Δ_θ` is `restrictedSimplex d θ` in `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm
is the `ℓ₁` norm. Lipschitz continuity over `Δ_θ` is
`|R(a) − R(b)| ≤ G_R ‖a − b‖₁` for `a, b ∈ Δ_θ`. `θ > 0` is required: `ln θ` is undefined at
`θ = 0` (and with Lean's `Real.log 0 = 0` the claim would be false there, since the entropy is not
Lipschitz on the whole simplex). No upper bound `θ ≤ 1/d` is needed: for `θ > 1/d` the set `Δ_θ`
is empty. -/
theorem lemma_4 {d : ℕ} (θ : ℝ) (hθ : 0 < θ) :
    ∀ a ∈ restrictedSimplex d θ, ∀ b ∈ restrictedSimplex d θ,
      |negEntropy a - negEntropy b| ≤ max |Real.log θ| 1 * ‖a - b‖ := by sorry

end OnlineSaddlePoint.Supplement
