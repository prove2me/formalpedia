-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_prop_5_4
-- name    : NonconvexDRS.ImageSmooth.prop_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:11.744847+00:00
-- url     : https://prove2.me/theorems/071a52e5-4871-416e-baf4-8a8cb64df964
-- title:
--   Proposition 5.4, p. 18 — the image of a proper lsc σ_h-strongly convex h under C is σ_h/‖C‖²-strongly convex
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\sigma_h$-strongly convex, $\sigma_h>0$. Then for every $C\in\mathbb R^{p\times n}$ the image function $(Ch)(s)=\inf\{h(x)\mid Cx=s\}$ is proper and $\sigma_{(Ch)}$-strongly convex with
--   $$\sigma_{(Ch)}=\frac{\sigma_h}{\|C\|^2}.$$
--
--   Theorem 5.13 uses this in cases (ii) and (iii) when $\sigma_f>0$, to obtain the hypoconvexity modulus $\sigma_f/\|A\|^2$ of $(Af)$.
--
--   **Formalization Note** Properness of $(Ch)$ is stated explicitly, so that the strong-convexity clause, which reads $(Ch)$ through `toReal` on its domain, is about a function that is never $-\infty$. For $C=0$ the page's modulus is $\sigma_h/0=\infty$, while Lean evaluates $\sigma_h/0=0$; then $\operatorname{dom}(Ch)=\{0\}$ is a single point, on which strong convexity with every modulus holds, so nothing is lost.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 18, Proposition 5.4 (proof p. 29)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proposition 5.4, p. 18: if `h : ℝⁿ → ℝ̄` is proper, lsc and `σ_h`-strongly convex (`σ_h > 0`),
then for every `C ∈ ℝ^{p×n}` the image function `(Ch)` is proper and `σ_h/‖C‖²`-strongly convex. -/
theorem prop_5_4 {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (hh : NonconvexDRS.DRS.IsProper h)
    (hlsc : LowerSemicontinuous h) (σh : ℝ) (hσh : 0 < σh) (hsc : IsStronglyConvexE h σh)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    NonconvexDRS.DRS.IsProper (imageFn C h) ∧ IsStronglyConvexE (imageFn C h) (σh / ‖C‖ ^ 2) := by sorry

end NonconvexDRS.ImageSmooth
