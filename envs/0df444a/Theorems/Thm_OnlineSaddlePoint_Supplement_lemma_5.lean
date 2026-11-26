-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_lemma_5
-- name    : OnlineSaddlePoint.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:55:18.527571+00:00
-- url     : https://prove2.me/theorems/c074d0e2-be3d-4605-a3a5-67cead0a3706
-- title:
--   Lemma 5 — every $\ell_1$-nearest point of $\Delta_\theta$ is within $2\theta(d-1)$ of $z^*\in\Delta$
-- statement:
--   Let $d\in\mathbb N$, $0\le\theta\le1/d$, and $z^*\in\Delta=\{z\in\mathbb R^d: z\ge0,\ \|z\|_1=1\}$. Let $z^*_p\in\Delta_\theta$ be a point of the restricted simplex nearest to $z^*$ in $\ell_1$, that is, $\|z^*_p-z^*\|_1\le\|z-z^*\|_1$ for every $z\in\Delta_\theta$. Then
--
--   $$
--   \|z^*_p-z^*\|_1\le 2\theta(d-1).
--   $$
--
--   Restricting a player to $\Delta_\theta$ therefore costs at most $2\theta(d-1)$ in $\ell_1$ distance; combined with Lemma 6 this bounds the change of the game value caused by the restriction in the proof of Theorem 3.
--
--   Differences from the source:
--   - generalization: $z^*_p\triangleq\arg\min_{z\in\Delta_\theta}\|z-z^*\|_1$, \"unique since it is a projection\" → every minimizer $z^*_p\in\Delta_\theta$ of $\|z-z^*\|_1$; uniqueness is not asserted; reason: $\ell_1$ nearest points need not be unique (for $d=3$, $\theta=0.1$, $z^*=(\frac12,\frac12,0)$ both $(0.45,0.45,0.1)$ and $(0.5,0.4,0.1)$ are at distance $0.2$, the minimum); the bound holds for each, so it covers the paper's $z^*_p$
--   - reading: $\theta\le\frac1d$ → $0\le\theta\le\frac1d$; reason: display (10) fixes $\theta\in[0,1/d]$; for $\theta<0$ and $d\ge2$ the right side is negative and the claim false
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
--   - encoding: $d-1$ → $(d:\mathbb R)-1$; reason: computed in $\mathbb R$; equal to the natural-number value since $\Delta\ne\emptyset$ forces $d\ge1$
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 5, p.17

import Mathlib
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex

namespace OnlineSaddlePoint.Supplement

/-- **Lemma 5 (`ℓ₁` distance to the restricted simplex).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 5, p.17: "Let `z* ∈ Δ ⊂ ℝ^d` define `z*_p ≜ arg min_{z∈Δ_θ} ‖z − z*‖₁`, with
`θ ≤ 1/d`. Notice `z*_p` is unique since it is a projection. It holds that `‖z*_p − z*‖₁ ≤ 2θ(d − 1)`."

**Formalization Note.** `Δ = restrictedSimplex d 0` and `Δ_θ = restrictedSimplex d θ` in
`PiLp 1 (fun _ : Fin d => ℝ)` (the `ℓ₁` norm). `θ ≥ 0` is the range `θ ∈ [0, 1/d]` of (10), p.16.
The aside "`z*_p` is unique since it is a projection" is not asserted: `ℓ₁` nearest points need not
be unique, and the bound is stated for every `z*_p ∈ Δ_θ` minimizing `‖z − z*‖₁` over `Δ_θ`. `d − 1`
is computed in `ℝ` (here `d ≥ 1`, since `Δ` is nonempty). -/
theorem lemma_5 {d : ℕ} (θ : ℝ) (zstar zp : PiLp 1 (fun _ : Fin d => ℝ))
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / (d : ℝ)) (hz : zstar ∈ restrictedSimplex d 0)
    (hzp : zp ∈ restrictedSimplex d θ ∧ ∀ z ∈ restrictedSimplex d θ, ‖zp - zstar‖ ≤ ‖z - zstar‖) :
    ‖zp - zstar‖ ≤ 2 * θ * ((d : ℝ) - 1) := by sorry

end OnlineSaddlePoint.Supplement
