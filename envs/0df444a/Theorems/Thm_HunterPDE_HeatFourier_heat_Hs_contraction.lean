-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heat_Hs_contraction
-- name    : HunterPDE.HeatFourier.heat_Hs_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:01:00.995294+00:00
-- url     : https://prove2.me/theorems/6f57cd3c-c6d4-4c6d-bc21-7666e7e10d35
-- title:
--   Theorem 5.9 — the heat flow is a contraction in every Hˢ: ‖u(t)‖_{Hˢ} ≤ ‖f‖_{Hˢ}
-- statement:
--   Let $f \in \mathcal S(\mathbb{R}^n)$ be real-valued and $u$ the Schwartz solution of the heat problem. Then for every $s \in \mathbb{R}$ and $t \ge 0$,
--   $$\|u(t)\|_{H^s} \le \|f\|_{H^s}.$$
--   This energy estimate is what allows the extension of the solution operator to generalized solutions with $H^s$ data (Theorem 5.12).
--
--   **Formalization Note.** $\|\cdot\|_{H^s}$ is the norm of Definition 5.74 in the book's Fourier normalization, valued in $[0,\infty]$; $u(t)$ and $f$ are viewed as complex-valued. The book assumes $u \in C^\infty([0,\infty);\mathcal S)$; the Lean hypothesis is the solution property of Theorem 5.4 ($C \cap C^1$), which by that theorem determines the same $u$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 135, Theorem 5.9

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_FourierTransform
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open scoped SchwartzMap

/-- Hunter, *Notes on PDEs*, p. 135, Theorem 5.9: if `f ∈ 𝓢` and `u` is the solution of (5.2)
(Theorem 5.4; it lies in `C^∞([0, ∞); 𝓢)`), then for every `s ∈ ℝ` and `t ≥ 0`,
`‖u(t)‖_{Hˢ} ≤ ‖f‖_{Hˢ}`,
with the `Hˢ` norm of Definition 5.74 in the book's Fourier normalization (`hsNorm`). -/
theorem heat_Hs_contraction (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))
    (u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hu : IsSchwartzHeatSolution (Set.Ici 0) f u)
    (s t : ℝ) (ht : 0 ≤ t) :
    hsNorm n s (fun x => ((u t x : ℝ) : ℂ)) ≤ hsNorm n s (fun x => ((f x : ℝ) : ℂ)) := by sorry

end HunterPDE.HeatFourier
