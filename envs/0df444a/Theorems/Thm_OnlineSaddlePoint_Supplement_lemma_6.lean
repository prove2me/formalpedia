-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_lemma_6
-- name    : OnlineSaddlePoint.Supplement.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:55:46.606695+00:00
-- url     : https://prove2.me/theorems/14cb28ab-a057-538f-be10-c9fc737a2901
-- title:
--   Lemma 6 — restricting both players to $\Delta_\theta$ moves the game value by at most $G_{\bar{\mathcal L}}T\|x_p-x^*\|_1$ / $G_{\bar{\mathcal L}}T\|y_p-y^*\|_1$
-- statement:
--   Let $d_1,d_2,T\in\mathbb N$ and $\theta\ge0$. Let $\bar{\mathcal L}_1,\dots,\bar{\mathcal L}_T$ be convex-concave on $\Delta_X\times\Delta_Y$ (the probability simplexes in $\mathbb R^{d_1}$, $\mathbb R^{d_2}$) and $G_{\bar{\mathcal L}}$-Lipschitz there with respect to $\|\cdot\|_1$. Let $(x^*,y^*)\in\Delta_X\times\Delta_Y$ be a saddle point of $\sum_{t=1}^T\bar{\mathcal L}_t$ on $\Delta_X\times\Delta_Y$, and let $x_p\in\Delta_{X,\theta}$, $y_p\in\Delta_{Y,\theta}$ be any points of the restricted simplexes. Then
--
--   $$
--   -G_{\bar{\mathcal L}}T\|x_p-x^*\|_1\ \le\ \min_{x\in\Delta_X}\max_{y\in\Delta_Y}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)-\min_{x\in\Delta_{X,\theta}}\max_{y\in\Delta_{Y,\theta}}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)\ \le\ G_{\bar{\mathcal L}}T\|y_p-y^*\|_1 .
--   $$
--
--   In the paper $x_p$, $y_p$ are the projections $x^*_p$, $y^*_p$ of the saddle point onto the restricted simplexes. The lemma shows that the comparator of the SP-Regret changes little when the players are confined to $\Delta_\theta$, which OMG-RFTL needs because its iterates live there.
--
--   Differences from the source:
--   - generalization: $x^*_p$, $y^*_p$ the projections (in $\|\cdot\|_\infty$, per the proof) of the saddle point onto $\Delta_{X,\theta}$, $\Delta_{Y,\theta}$ → any $x_p\in\Delta_{X,\theta}$, $y_p\in\Delta_{Y,\theta}$; reason: the proof uses only this membership; the projections are such points, and so are the $\ell_1$ projections of Lemma 5 that the proof of Theorem 3 combines with it
--   - reading: $(x^*,y^*)$ introduced only in the proof → every saddle point $(x^*,y^*)\in\Delta_X\times\Delta_Y$ of $\sum_t\bar{\mathcal L}_t$ (Mathlib `IsSaddlePointOn`); reason: the proof says \"Let $(x^*,y^*)$ be any saddle point pair\"
--   - reading: $\theta$ unspecified in the lemma → $\theta\ge0$; reason: display (10) fixes $\theta\in[0,1/d]$; $\theta\ge0$ gives $\Delta_{\cdot,\theta}\subseteq\Delta$, where the payoffs are assumed convex-concave and Lipschitz; the upper bound $\theta\le1/d$ is implied by $x_p\in\Delta_{X,\theta}$
--   - encoding: $G_{\bar{\mathcal L}}$-Lipschitz with respect to $\|\cdot\|_1$ on $\Delta_X\times\Delta_Y$ → `IsLipschitzPayoff` on $\Delta_X\times\Delta_Y$ in `PiLp 1`: $|\bar{\mathcal L}(x_1,y_1)-\bar{\mathcal L}(x_2,y_2)|\le G_{\bar{\mathcal L}}(\|x_1-x_2\|_1+\|y_1-y_2\|_1)$, $G_{\bar{\mathcal L}}\ge0$; reason: the $\ell_1$ norm of the stacked vector is exactly $\|x\|_1+\|y\|_1$; a Lipschitz constant is nonnegative
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
--   - encoding: $\bar{\mathcal L}_t:\Delta_X\times\Delta_Y\to\mathbb R$, $\min\max$ → functions on $\mathbb R^{d_1}\times\mathbb R^{d_2}$ whose values on the simplexes alone enter; `sInf`/`sSup` of images; reason: under continuity on the compact simplexes the extrema are attained
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 6, p.17 (proof p.17)

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff
import Definitions.Def_OnlineSaddlePoint_minimaxValue
import Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex

namespace OnlineSaddlePoint.Supplement

open OnlineSaddlePoint

/-- **Lemma 6 (restricting to `Δ_θ` changes the game value little).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 6, p.17: "Let `{𝓛̄_t(x, y)}_{t=1}^T` be an arbitrary sequence of
convex-concave functions, `𝓛̄_t : Δ_X × Δ_Y → ℝ`, that are `G_𝓛̄`-Lipschitz with respect to `‖·‖₁`. It
holds that `−G_𝓛̄ T ‖x*_p − x*‖₁ ≤ min_{x∈Δ_X} max_{y∈Δ_Y} ∑_{t=1}^T 𝓛̄_t(x, y) −
min_{x∈Δ_{X,θ}} max_{y∈Δ_{Y,θ}} ∑_{t=1}^T 𝓛̄_t(x, y) ≤ G_𝓛̄ T ‖y*_p − y*‖₁`."
In the proof (p.17), `(x*, y*)` is "any saddle point pair for `∑_{t=1}^T 𝓛̄_t(x, y)` with
`x* ∈ Δ_X`, `y* ∈ Δ_Y`" and `x*_p`, `y*_p` are its projections onto `Δ_{X,θ}`, `Δ_{Y,θ}`.

**Formalization Note.** The bound is stated for every saddle point `(x*, y*)` of `∑ 𝓛̄_t` on
`Δ_X × Δ_Y` and for every `x_p ∈ Δ_{X,θ}`, `y_p ∈ Δ_{Y,θ}`; the projections of the proof are such
points (the proof uses only this membership). `θ ≥ 0` is the range of (10), p.16, and makes
`Δ_{·,θ} ⊆ Δ`. Simplexes are `restrictedSimplex d θ` in `PiLp 1 (fun _ : Fin d => ℝ)` (`ℓ₁` norm); the
Lipschitz hypothesis is `IsLipschitzPayoff` on `Δ_X × Δ_Y`, the `ℓ₁` norm of the stacked vector. -/
theorem lemma_6 {d₁ d₂ : ℕ} (θ Gbar : ℝ) (T : ℕ)
    (Lbar : ℕ → PiLp 1 (fun _ : Fin d₁ => ℝ) → PiLp 1 (fun _ : Fin d₂ => ℝ) → ℝ)
    (xs xp : PiLp 1 (fun _ : Fin d₁ => ℝ)) (ys yp : PiLp 1 (fun _ : Fin d₂ => ℝ))
    (hθ : 0 ≤ θ)
    (hcc : ∀ t ∈ Finset.Icc 1 T,
      IsConvexConcaveOn (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) (Lbar t))
    (hlip : ∀ t ∈ Finset.Icc 1 T,
      IsLipschitzPayoff (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) Gbar (Lbar t))
    (hxs : xs ∈ restrictedSimplex d₁ 0) (hys : ys ∈ restrictedSimplex d₂ 0)
    (hsp : IsSaddlePointOn (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) (cumPayoff Lbar T)
      xs ys)
    (hxp : xp ∈ restrictedSimplex d₁ θ) (hyp : yp ∈ restrictedSimplex d₂ θ) :
    -(Gbar * T * ‖xp - xs‖) ≤
        minimaxValue (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) (cumPayoff Lbar T) -
          minimaxValue (restrictedSimplex d₁ θ) (restrictedSimplex d₂ θ) (cumPayoff Lbar T) ∧
      minimaxValue (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) (cumPayoff Lbar T) -
          minimaxValue (restrictedSimplex d₁ θ) (restrictedSimplex d₂ θ) (cumPayoff Lbar T) ≤
        Gbar * T * ‖yp - ys‖ := by sorry

end OnlineSaddlePoint.Supplement
