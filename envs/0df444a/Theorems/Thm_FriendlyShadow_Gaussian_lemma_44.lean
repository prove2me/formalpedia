-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_44
-- name    : FriendlyShadow.Gaussian.lemma_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:03.083935+00:00
-- url     : https://prove2.me/theorems/2380de5d-1f66-465b-968d-de3b55666206
-- title:
--   Lemma 44, pp. 33–34 — Laplace–Gaussian tails: Pr[‖X‖ ≥ σt] ≤ e^{−rt/4} (t ≥ r), Pr[|Xᵀθ| ≥ σt] ≤ e^{−rt/4} or 3e^{−t²/4}
-- statement:
--   Let $n\ge d\ge3$, $\sigma>0$, $c\ge4$, $r=c\sqrt{d\log n}$, and let $X\sim LG_d(0,\sigma,r)$ be $(\sigma,r)$-Laplace–Gaussian distributed with mean $0$. Then
--   $$\Pr[\|X\|\ge\sigma t]\le e^{-\frac14 rt}\qquad\text{for } t\ge r, \tag{19}$$
--   and for every unit vector $\theta$ and $t\ge0$,
--   $$\Pr[|X^\mathsf{T}\theta|\ge\sigma t]\le\begin{cases}e^{-\frac14 rt} & t\ge r,\\ 3e^{-t^2/4} & 0\le t\le r.\end{cases}\tag{20}$$
--
--   These tail bounds give the cutoff radius and $n$-th deviation estimates of Lemma 45 and the comparison of Lemma 46.
--
--   **Formalization Note** $\log$ is the natural logarithm. The page states the lemma inside §3, which assumes $n\ge d\ge3$ throughout; this standing assumption is carried (it guarantees $\log n>0$, so that $r>0$ and the distribution is defined). Both cases of (20) are asserted at $t=r$, where the page's case split overlaps.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 44, (19)–(20), pp. 33–34; Def 43, p. 33

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 44 (Laplace–Gaussian tail bounds, pp. 33–34). Let `X ∼ LG_d(0, σ, r)` with
`r = c√(d log n)`, `c ≥ 4`. Then (19) `Pr[‖X‖ ≥ σt] ≤ e^{−rt/4}` for `t ≥ r`, and (20) for every
unit vector `θ` and `t ≥ 0`, `Pr[|Xᵀθ| ≥ σt] ≤ e^{−rt/4}` if `t ≥ r` and `≤ 3e^{−t²/4}` if
`0 ≤ t ≤ r`. -/
theorem lemma_44 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (σ : ℝ) (hσ : 0 < σ) (c : ℝ)
    (hc : 4 ≤ c) (r : ℝ) (hr : r = c * Real.sqrt (d * Real.log n)) :
    (∀ t : ℝ, r ≤ t →
      lg (0 : EuclideanSpace ℝ (Fin d)) σ r {x | σ * t ≤ ‖x‖} ≤
        ENNReal.ofReal (Real.exp (-(1 / 4) * r * t))) ∧
    (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 → ∀ t : ℝ, 0 ≤ t →
      (r ≤ t →
        lg 0 σ r {x | σ * t ≤ |⟪x, θ⟫|} ≤ ENNReal.ofReal (Real.exp (-(1 / 4) * r * t))) ∧
      (t ≤ r →
        lg 0 σ r {x | σ * t ≤ |⟪x, θ⟫|} ≤ ENNReal.ofReal (3 * Real.exp (-(t ^ 2) / 4)))) := by sorry

end FriendlyShadow.Gaussian
