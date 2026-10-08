-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_theorem_9_6
-- name    : GoldieRenewal.Rates.theorem_9_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:38.380803+00:00
-- url     : https://prove2.me/theorems/167ef028-1e85-46e9-ba8c-9f61b290f551
-- title:
--   Theorem 9.6 — Beurling–Ganelius Tauberian remainder theorem: K ∗ f = O(e^{−βx}) ⇒ f = O(e^{−βx/(p+1)})
-- statement:
--   Let $K\in L^1(\mathbb R)$ be such that $\hat K(\xi)=\int e^{i\xi t}K(t)\,dt$ does not vanish for real $\xi$. Suppose there are constants $p>\tfrac12$, $a>0$, $C$ and a function $w$ holomorphic in the strip $-a<\Im\zeta<0$ such that
--   $$|w'(\zeta)|<C(1+|\zeta|)^{p-1}\quad(-a<\Im\zeta<0),\qquad \lim_{\eta\downarrow0}w(\xi-i\eta)=\frac1{\hat K(\xi)}\quad(\xi\in\mathbb R).$$
--   Let $0<\beta<a$ and let $f:\mathbb R\to\mathbb R$ be bounded, measurable, and satisfy the Tauberian condition
--   $$f(x)-f(x+y)\le Ae^{-\beta x/(p+1)},\qquad 0\le y\le e^{-\beta x/(p+1)},\ x>x_0,$$
--   for some constants $A,x_0$. If $K*f(x)=\int K(x-u)f(u)\,du=O(e^{-\beta x})$ as $x\to\infty$, then $f(x)=O(e^{-\beta x/(p+1)})$ as $x\to\infty$.
--
--   The theorem converts a remainder estimate for a smoothed function into one for the function itself; in the proof of Theorem 3.2 it is applied with $p=1$, which is where the exponent $\beta/2$ comes from.
--
--   **Formalization Note** $K$ is complex valued (the paper does not restrict it). $a$ is a finite real number; the paper's application with $a=\infty$ is covered by restricting $w$ to any finite strip with $a>\beta$. Measurability of $f$ is implicit in the paper and needed for $K*f$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 155, Theorem 9.6 (quoting Ganelius 1962), (9.25)

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms

open MeasureTheory Complex Filter Asymptotics Topology

namespace GoldieRenewal.Rates

/-- **Theorem 9.6** (Goldie 1991, p. 155; Beurling–Ganelius Tauberian remainder theorem,
Ganelius 1962, quoted without proof). Let `K ∈ L¹(ℝ)` with `K̂(ξ) ≠ 0` for real `ξ`, and suppose
there are constants `p > 1/2`, `a > 0`, `C` and a function `w` holomorphic in the strip
`−a < ℑζ < 0` with `|w′(ζ)| < C(1 + |ζ|)^{p−1}` there and `lim_{η↓0} w(ξ − iη) = 1/K̂(ξ)` for
real `ξ`. Let `0 < β < a` and let `f : ℝ → ℝ` be bounded and satisfy the Tauberian condition
(9.25) `f(x) − f(x + y) ≤ A e^{−βx/(p+1)}` for `0 ≤ y ≤ e^{−βx/(p+1)}`, `x > x₀`. Then
`K ∗ f(x) = O(e^{−βx})` implies `f(x) = O(e^{−βx/(p+1)})`, `x → ∞`.
Formalization Note: `K` is complex valued (the paper does not restrict it), `K̂ = fourierTransform K`
(`+i` sign, p. 128), `K ∗ f(x) = ∫ K(x − u) f(u) du`. `a` is a finite real; the paper's
application with `a = ∞` (p. 154) is covered by restricting `w` to any finite strip with
`a > β`. `f` is assumed measurable (implicit in the paper, needed for `K ∗ f`). The constants
`A`, `x₀` of (9.25) are universally quantified parameters (equivalent to "for some"). -/
theorem theorem_9_6 (K : ℝ → ℂ) (hK : Integrable K)
    (hK_ne : ∀ ξ : ℝ, fourierTransform K ξ ≠ 0)
    (p a C : ℝ) (hp : 1 / 2 < p) (ha : 0 < a) (w : ℂ → ℂ)
    (hw_holo : DifferentiableOn ℂ w {ζ : ℂ | -a < ζ.im ∧ ζ.im < 0})
    (hw_deriv : ∀ ζ : ℂ, -a < ζ.im → ζ.im < 0 → ‖deriv w ζ‖ < C * (1 + ‖ζ‖) ^ (p - 1))
    (hw_lim : ∀ ξ : ℝ, Tendsto (fun η : ℝ => w ((ξ : ℂ) - I * (η : ℂ))) (𝓝[>] 0)
      (𝓝 (1 / fourierTransform K ξ)))
    (β : ℝ) (hβ : 0 < β) (hβa : β < a)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (A x₀ : ℝ)
    (h_taub : ∀ x : ℝ, x₀ < x → ∀ y : ℝ, 0 ≤ y → y ≤ Real.exp (-(β * x) / (p + 1)) →
      f x - f (x + y) ≤ A * Real.exp (-(β * x) / (p + 1)))
    (h_conv : (fun x : ℝ => ∫ u : ℝ, K (x - u) * (f u : ℂ)) =O[atTop]
      (fun x : ℝ => Real.exp (-(β * x)))) :
    f =O[atTop] (fun x : ℝ => Real.exp (-(β * x) / (p + 1))) := by sorry

end GoldieRenewal.Rates
