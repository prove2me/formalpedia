-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_schrodinger_Hs_conservation
-- name    : HunterPDE.HeatFourier.schrodinger_Hs_conservation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:05:17.540987+00:00
-- url     : https://prove2.me/theorems/192d132d-09a0-4510-909c-4248d7a3adfd
-- title:
--   Theorem 5.17 — the Schrödinger flow conserves every Hˢ norm
-- statement:
--   Let $f \in \mathcal S(\mathbb{R}^n;\mathbb{C})$ and let $u \in C^\infty(\mathbb{R};\mathcal S)$ be the solution of $iu_t = -\Delta u$, $u(0) = f$. Then for every $s \in \mathbb{R}$
--   $$\|u(t)\|_{H^s} = \|f\|_{H^s} \qquad \text{for every } t \in \mathbb{R}.$$
--   In contrast with the heat equation there is no smoothing: the $H^s$ norm is exactly conserved in both time directions.
--
--   **Formalization Note.** $\|\cdot\|_{H^s}$ is the norm of Definition 5.74 (book normalization), valued in $[0,\infty]$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 139, Theorem 5.17

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_FourierTransform
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open scoped SchwartzMap

/-- Hunter, *Notes on PDEs*, p. 139, Theorem 5.17: if `f ∈ 𝓢` and `u ∈ C^∞(ℝ; 𝓢)` is the solution
of (5.13), then for every `s ∈ ℝ`, `‖u(t)‖_{Hˢ} = ‖f‖_{Hˢ}` for every `t ∈ ℝ`
(`Hˢ` norm of Definition 5.74, book normalization). -/
theorem schrodinger_Hs_conservation (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hu : IsSchwartzSchrodingerSolution f u)
    (hsmooth : IsStrongSmoothOn u Set.univ) (s t : ℝ) :
    hsNorm n s (u t) = hsNorm n s f := by sorry

end HunterPDE.HeatFourier
