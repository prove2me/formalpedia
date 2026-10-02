-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heat_parabolic_estimate
-- name    : HunterPDE.HeatFourier.heat_parabolic_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:01:36.654299+00:00
-- url     : https://prove2.me/theorems/186844ad-7bc5-40dc-a0e9-86c71fdb39fc
-- title:
--   Theorem 5.10 — ‖u‖_{C([0,T];Hˢ)} ≤ ‖f‖_{Hˢ} and ‖Du‖_{L²([0,T];Hˢ)} ≤ (1/√2)‖f‖_{Hˢ}
-- statement:
--   Let $T > 0$, let $f \in \mathcal S(\mathbb{R}^n)$ be real-valued and let $u$ be the Schwartz solution of the heat problem on $[0,T]$. Then for every $s \in \mathbb{R}$
--   $$\|u\|_{C([0,T];H^s)} = \max_{t\in[0,T]} \|u(t)\|_{H^s} \le \|f\|_{H^s}, \qquad \|Du\|_{L^2([0,T];H^s)} = \Big(\int_0^T \|Du(t)\|_{H^s}^2\,dt\Big)^{1/2} \le \frac{1}{\sqrt 2}\,\|f\|_{H^s},$$
--   where $\|Du(t)\|_{H^s}^2 = \sum_{i=1}^n \|\partial_i u(t)\|_{H^s}^2$. The second inequality is the parabolic gain of one spatial derivative in $L^2$ in time; it is the estimate later used for Galerkin approximations of general parabolic equations.
--
--   **Formalization Note.** The solution is `IsSchwartzHeatSolution (Set.Icc 0 T) f u` (continuous on $[0,T]$ in $\mathcal S$, $C^1$ on $(0,T)$); the book's hypothesis $u \in C^\infty([0,T];\mathcal S)$ is a property of that same solution. The maximum bound is stated for every $t\in[0,T]$. $\partial_i u(t)(x) = Du(t)(x)\,e_i$ with 0-based coordinates `i : Fin n`. Norms are $[0,\infty]$-valued and the time integral is a lower Lebesgue integral over $[0,T]$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 135, Theorem 5.10

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_FourierTransform
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open MeasureTheory
open scoped SchwartzMap ENNReal

/-- Hunter, *Notes on PDEs*, p. 135, Theorem 5.10 (energy and parabolic estimates): let `T > 0`,
`f ∈ 𝓢` and `u` the solution of (5.2) on `[0, T]` (`u ∈ C([0, T]; 𝓢) ∩ C¹(0, T; 𝓢)`; it lies in
`C^∞([0, T]; 𝓢)`). Then for every `s ∈ ℝ`
`‖u‖_{C([0,T]; Hˢ)} = max_{t ∈ [0,T]} ‖u(t)‖_{Hˢ} ≤ ‖f‖_{Hˢ}` and
`‖Du‖_{L²([0,T]; Hˢ)} = (∫₀ᵀ ‖Du(t)‖²_{Hˢ} dt)^{1/2} ≤ (1/√2) ‖f‖_{Hˢ}`,
where `‖Du(t)‖²_{Hˢ} = Σᵢ ‖∂ᵢu(t)‖²_{Hˢ}` and `∂ᵢu(t)(x) = Du(t)(x) eᵢ` (0-based `i : Fin n`).
The maximum bound is stated for every `t ∈ [0, T]`. Norms are `hsNorm` (Definition 5.74, book
normalization), the time integral a lower Lebesgue integral. -/
theorem heat_parabolic_estimate (n : ℕ) (T : ℝ) (hT : 0 < T)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))
    (u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hu : IsSchwartzHeatSolution (Set.Icc 0 T) f u)
    (s : ℝ) :
    (∀ t ∈ Set.Icc 0 T,
      hsNorm n s (fun x => ((u t x : ℝ) : ℂ)) ≤ hsNorm n s (fun x => ((f x : ℝ) : ℂ))) ∧
    (∫⁻ t in Set.Icc 0 T, ∑ i : Fin n,
        hsNorm n s (fun x => ((fderiv ℝ (u t) x (EuclideanSpace.single i 1) : ℝ) : ℂ)) ^ 2)
          ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (1 / Real.sqrt 2) * hsNorm n s (fun x => ((f x : ℝ) : ℂ)) := by sorry

end HunterPDE.HeatFourier
