-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heat_schwartz_ivp
-- name    : HunterPDE.HeatFourier.heat_schwartz_ivp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:59:24.262853+00:00
-- url     : https://prove2.me/theorems/a6233ab8-ee9a-499d-b80a-5fbfbcae4203
-- title:
--   Theorem 5.4 — heat IVP with Schwartz data: existence, uniqueness, C^∞([0,∞);S), û = f̂ e^{−t|k|²} and u = Γ(·,t) ∗ f
-- statement:
--   Let $f \in \mathcal S(\mathbb{R}^n)$ be real-valued. There is a unique solution
--   $$u \in C([0,\infty);\mathcal S) \cap C^1(0,\infty;\mathcal S)$$
--   of $u_t = \Delta u$ ($t>0$), $u(0) = f$. Moreover $u \in C^\infty([0,\infty);\mathcal S)$, its spatial Fourier transform is
--   $$\hat u(k,t) = \hat f(k)\, e^{-t|k|^2} \qquad (t \ge 0),$$
--   and for $t > 0$ it is given by the heat convolution $u(x,t) = \int_{\mathbb{R}^n} \Gamma(x-y,t) f(y)\,dy$.
--
--   This is the basic well-posedness result for the heat equation with smooth, rapidly decreasing data, and the source of the explicit solution formulas used in the rest of the chapter.
--
--   **Formalization Note.** Solutions are Schwartz-valued curves in the sense of Definitions 5.1–5.2 (`IsSchwartzHeatSolution (Set.Ici 0) f u`); uniqueness is stated as agreement at every $t \ge 0$, since values at $t<0$ are irrelevant. The Fourier transform is the book's (5.73), applied to $u(t)$ and $f$ viewed as complex-valued functions.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 129–130, Theorem 5.4

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_HeatKernel
import Definitions.Def_HunterPDE_HeatFourier_FourierTransform
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open scoped SchwartzMap

/-- Hunter, *Notes on PDEs*, pp. 129–130, Theorem 5.4 (heat equation with Schwartz data). For
real-valued `f ∈ 𝓢(ℝⁿ)`:
* there is a solution `u ∈ C([0, ∞); 𝓢) ∩ C¹(0, ∞; 𝓢)` of (5.2) (`IsSchwartzHeatSolution`);
* it is unique: two such solutions agree at every `t ≥ 0`;
* every such solution satisfies `u ∈ C^∞([0, ∞); 𝓢)`, has spatial Fourier transform
  `û(k, t) = f̂(k) e^{−t|k|²}` (5.4) for `t ≥ 0` (the book's transform (5.73), applied to `u(t)` and
  `f` as complex-valued functions), and for `t > 0` is given by
  `u(x, t) = ∫ Γ(x − y, t) f(y) dy` (5.5) with the heat kernel (5.6). -/
theorem heat_schwartz_ivp (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :
    (∃ u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ), IsSchwartzHeatSolution (Set.Ici 0) f u) ∧
    (∀ u v : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ),
      IsSchwartzHeatSolution (Set.Ici 0) f u → IsSchwartzHeatSolution (Set.Ici 0) f v →
        ∀ t : ℝ, 0 ≤ t → u t = v t) ∧
    (∀ u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ), IsSchwartzHeatSolution (Set.Ici 0) f u →
      IsStrongSmoothOn u (Set.Ici 0) ∧
      (∀ (t : ℝ), 0 ≤ t → ∀ k : EuclideanSpace ℝ (Fin n),
        fourierTransform n (fun x => ((u t x : ℝ) : ℂ)) k =
          fourierTransform n (fun x => ((f x : ℝ) : ℂ)) k * ((Real.exp (-t * ‖k‖ ^ 2) : ℝ) : ℂ)) ∧
      (∀ (t : ℝ), 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
        u t x = ∫ y, heatKernel n (x - y) t * f y)) := by sorry

end HunterPDE.HeatFourier
