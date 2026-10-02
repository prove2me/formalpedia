-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_schrodinger_schwartz_ivp
-- name    : HunterPDE.HeatFourier.schrodinger_schwartz_ivp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:03:12.835169+00:00
-- url     : https://prove2.me/theorems/4ac88831-dc8b-4c62-87ff-f5c08ac4dbc6
-- title:
--   Theorem 5.15 — Schrödinger IVP with Schwartz data: unique C^∞(ℝ;S) solution, û = e^{−it|k|²} f̂, kernel (4πit)^{−n/2} e^{i|x|²/4t}
-- statement:
--   For every $f \in \mathcal S(\mathbb{R}^n;\mathbb{C})$ there is a unique solution $u \in C^\infty(\mathbb{R};\mathcal S)$ of
--   $$i u_t = -\Delta u \quad (t \in \mathbb{R}), \qquad u(0) = f.$$
--   Its spatial Fourier transform is $\hat u(k,t) = e^{-it|k|^2}\hat f(k)$ for all $t$, and for $t \ne 0$
--   $$u(x,t) = \int_{\mathbb{R}^n} \Gamma(x-y,t)\, f(y)\,dy, \qquad \Gamma(x,t) = \frac{1}{(4\pi i t)^{n/2}}\, e^{\,i|x|^2/4t}.$$
--   Unlike the heat equation, the Schrödinger equation is solvable forward and backward in time, with oscillating instead of decaying Fourier modes.
--
--   **Formalization Note.** $(4\pi i t)^{n/2}$ is the principal-branch complex power. The book prints $e^{-i|x|^2/4t}$; that sign is a misprint (it is incompatible with $\hat u = e^{-it|k|^2}\hat f$, since $u_t = i\Delta u$ has kernel $(4\pi i t)^{-n/2}e^{-|x|^2/(4it)}$), and the corrected sign is used. Uniqueness is among solutions in $C^\infty(\mathbb{R};\mathcal S)$, as in the book. The Fourier transform is the book's (5.73).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 138, Theorem 5.15

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_HeatKernel
import Definitions.Def_HunterPDE_HeatFourier_FourierTransform
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open scoped SchwartzMap

/-- Hunter, *Notes on PDEs*, p. 138, Theorem 5.15 (Schrödinger equation with Schwartz data). For
`f ∈ 𝓢(ℝⁿ, ℂ)`:
* there is a solution `u ∈ C^∞(ℝ; 𝓢)` of (5.13) `i uₜ = −Δu`, `u(0) = f`;
* it is unique among solutions in `C^∞(ℝ; 𝓢)`;
* its spatial Fourier transform is `û(k, t) = e^{−it|k|²} f̂(k)` (5.15) for every `t ∈ ℝ` (book
  normalization (5.73)), and for `t ≠ 0`, `u(x, t) = ∫ Γ(x − y, t) f(y) dy` with
  `Γ(x, t) = (4πit)^{−n/2} e^{+i|x|²/4t}` (principal branch).
The book prints `e^{−i|x|²/4t}`; that sign is a misprint (it contradicts (5.15)); the corrected
kernel is `schrodingerKernel`. -/
theorem schrodinger_schwartz_ivp (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (∃ u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      IsSchwartzSchrodingerSolution f u ∧ IsStrongSmoothOn u Set.univ) ∧
    (∀ u v : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      IsSchwartzSchrodingerSolution f u → IsStrongSmoothOn u Set.univ →
      IsSchwartzSchrodingerSolution f v → IsStrongSmoothOn v Set.univ → u = v) ∧
    (∀ u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      IsSchwartzSchrodingerSolution f u → IsStrongSmoothOn u Set.univ →
      (∀ (t : ℝ) (k : EuclideanSpace ℝ (Fin n)),
        fourierTransform n (u t) k =
          Complex.exp (-(Complex.I * ((t * ‖k‖ ^ 2 : ℝ) : ℂ))) * fourierTransform n f k) ∧
      (∀ (t : ℝ), t ≠ 0 → ∀ x : EuclideanSpace ℝ (Fin n),
        u t x = ∫ y, schrodingerKernel n (x - y) t * f y)) := by sorry

end HunterPDE.HeatFourier
