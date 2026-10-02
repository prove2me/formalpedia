-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heat_Lp_smoothing
-- name    : HunterPDE.HeatFourier.heat_Lp_smoothing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:02:15.358287+00:00
-- url     : https://prove2.me/theorems/e8748018-254a-43e6-9440-f1c1023b8956
-- title:
--   Theorem 5.5 — for f ∈ Lᵖ(ℝⁿ), u = Γ(·,t) ∗ f is smooth, solves u_t = Δu, decays with all derivatives and tends to f in Lᵖ (p < ∞)
-- statement:
--   Let $1 \le p \le \infty$ and $f \in L^p(\mathbb{R}^n)$ real-valued, and define $u : \mathbb{R}^n \times (0,\infty) \to \mathbb{R}$ by
--   $$u(x,t) = \int_{\mathbb{R}^n} \Gamma(x-y,t)\, f(y)\,dy, \qquad \Gamma(x,t) = \frac{1}{(4\pi t)^{n/2}} e^{-|x|^2/4t}.$$
--   Then the integral converges absolutely for all $x$ and $t > 0$, $u$ is $C^\infty$ on $\mathbb{R}^n \times (0,\infty)$, and $u_t = \Delta u$ for $t > 0$. If $1 \le p < \infty$, then moreover for each $t > 0$ every derivative of $u$ (in $(x,t)$, of every order) tends to $0$ as $|x| \to \infty$, and
--   $$u(\cdot,t) \to f \quad \text{in } L^p \text{ as } t \to 0^+ .$$
--   This is the smoothing property of the heat equation: rough $L^p$ data become instantly smooth and decaying, while the initial condition is recovered in the $L^p$ sense.
--
--   **Formalization Note.** The book writes $u \in C_0^\infty(\mathbb{R}^n\times(0,\infty))$ and its proof explains this as "all of these derivatives approach zero as $|x| \to \infty$"; it is formalized in that sense (at fixed $t>0$, joint derivatives `iteratedFDeriv` of every order, along the cocompact filter of $\mathbb{R}^n$). The book asserts this decay also for $p=\infty$, where it fails ($f \equiv 1$ gives $u \equiv 1$); here it is stated for $p < \infty$ only. $\Delta$ is Mathlib's Laplacian in $x$; the $L^p$ convergence is `eLpNorm (u(·,t) − f) p → 0` along $t \to 0^+$. `MemLp f p` includes a.e.-strong measurability.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 131, Theorem 5.5

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_HeatKernel

namespace HunterPDE.HeatFourier

open MeasureTheory Filter Topology
open scoped ContDiff Laplacian ENNReal

/-- Hunter, *Notes on PDEs*, p. 131, Theorem 5.5 (smoothing by the heat kernel). Let
`1 ≤ p ≤ ∞` and `f ∈ Lᵖ(ℝⁿ)` real-valued, and let `u(x, t) = ∫ Γ(x − y, t) f(y) dy` (5.5) with the
heat kernel `Γ` of (5.6). Then:
* the integral (5.5) converges absolutely for every `x` and every `t > 0`;
* `u` is `C^∞` on `ℝⁿ × (0, ∞)` (jointly in `(x, t)`);
* `uₜ = Δu` for `t > 0` (Laplacian in `x`);
* if `p < ∞`: for every `t > 0` every derivative of `u` of every order `k` (in `(x, t)`) tends to
  `0` as `|x| → ∞` (this is the book's `u ∈ C_0^∞(ℝⁿ × (0, ∞))`, read as in the proof: "all of these
  derivatives approach zero as `|x| → ∞`"), and `u(·, t) → f` in `Lᵖ` as `t → 0⁺`.
The book asserts the decay for `p = ∞` as well; that is false (`f ≡ 1 ∈ L^∞` gives `u ≡ 1`), so
here it is stated for `p < ∞` only, where the book's proof (Hölder with `Γ(·, t) ∈ L^{p'}`) gives it. -/
theorem heat_Lp_smoothing (n : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f p volume) :
    (∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      Integrable (fun y => heatKernel n (x - y) t * f y)) ∧
    ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n f z.1 z.2)
      (Set.univ ×ˢ Set.Ioi 0) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      deriv (fun s : ℝ => heatSolution n f x s) t = Δ (fun y => heatSolution n f y t) x) ∧
    (p ≠ ⊤ →
      (∀ (k : ℕ) (t : ℝ), 0 < t →
        Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
          ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n f z.1 z.2)
            (x, t)‖) (cocompact _) (𝓝 0)) ∧
      Tendsto (fun t : ℝ => eLpNorm (fun x => heatSolution n f x t - f x) p volume)
        (𝓝[>] 0) (𝓝 0)) := by sorry

end HunterPDE.HeatFourier
