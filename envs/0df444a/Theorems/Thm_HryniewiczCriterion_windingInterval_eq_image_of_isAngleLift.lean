-- Prove2me | Theorems.Thm_HryniewiczCriterion_windingInterval_eq_image_of_isAngleLift
-- name    : HryniewiczCriterion.windingInterval_eq_image_of_isAngleLift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:43:48.995328+00:00
-- url     : https://prove2.me/theorems/acea5c8c-cf09-455e-a797-bc30150e9d2d
-- title:
--   The winding interval is computed by any family of angle lifts
-- statement:
--   Let $\varphi:\mathbb{R}\to\mathbb{R}^{2\times 2}$ and let $\theta:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$ be such that, for every $s\in\mathbb{R}$, $t\mapsto\theta(s,t)$ is an angle lift of $t\mapsto\varphi(t)e^{is}$ on $[0,1]$ starting at $s$: it is continuous on $[0,1]$, $\theta(s,0)=s$, and $\varphi(t)e^{is}=r\,e^{i\theta(s,t)}$ with $r>0$ for all $t\in[0,1]$. Then Hryniewicz's winding interval of $\varphi$ is
--   $$I(\varphi)=\Big\{\tfrac{\theta(s,1)-s}{2\pi}\ :\ s\in[0,2\pi]\Big\}.$$
--
--   In other words, the winding interval can be computed from any one family of angle lifts. This makes $I(\varphi)$, and hence the Conley–Zehnder index `czIndexOfPath`, accessible from a family of continuous arguments constructed by other means (for example from an ODE).
--
--   **Formalization Note** Angle lifts are `HryniewiczCriterion.IsAngleLift φ s (θ s)`, and the winding interval is `HryniewiczCriterion.windingInterval φ`. No regularity or symplecticity of $\varphi$ is assumed.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1 (winding interval of a symplectic path)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open HryniewiczCriterion

/-- If for every `s` the function `θ s` is an angle lift of `t ↦ φ(t) e^{is}` starting at `s`, then
the winding interval of `φ` is the image of `s ↦ (θ s 1 - s) / 2π` on `[0, 2π]`. -/
theorem HryniewiczCriterion.windingInterval_eq_image_of_isAngleLift
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ → ℝ → ℝ) (hθ : ∀ s, IsAngleLift φ s (θ s)) :
    windingInterval φ =
      (fun s => (θ s 1 - s) / (2 * Real.pi)) '' Set.Icc 0 (2 * Real.pi) := by sorry
