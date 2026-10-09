-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_eq_3_11
-- name    : GhadimiLan.RSGF.eq_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:27.288838+00:00
-- url     : https://prove2.me/theorems/cdd68460-9d65-4c8f-933c-dedf35a32af3
-- title:
--   (3.11), p. 16 — −µ²Ln ≤ [f_µ(x) − f*_µ] − [f(x) − f*] ≤ µ²Ln
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable with $L$-Lipschitz gradient, $L \ge 0$, and bounded below with infimum $f^*$. Let $\mu > 0$, let $f_\mu$ be the Gaussian smoothing (3.3), and let $f_\mu^* = \inf_x f_\mu(x)$ (3.10). Then for every $x \in \mathbb R^n$,
--   $$
--   -\mu^2 L n \le [f_\mu(x) - f_\mu^*] - [f(x) - f^*] \le \mu^2 L n .
--   $$
--
--   The optimality gap of the smoothed function is within $\mu^2 L n$ of that of $f$. The proof of Theorem 3.2 uses this to replace $f_\mu(x_1) - f_\mu^*$ by $f(x_1) - f^* + \mu^2 L n$.
--
--   **Formalization Note** The paper writes $f^*_\mu := \min_x f_\mu(x)$, but the minimum need not be attained. The Lean statement takes $f^*_\mu$ to be the infimum (`IsGLB` of the range of $f_\mu$), which exists because $f_\mu \ge f - \mu^2 L n/2$ by (3.5). The smoothing parameter is `μs`.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eqs. (3.10)–(3.11), p. 16

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Eq. (3.11) (Ghadimi & Lan, arXiv:1309.5549v1, p. 16): for `f ∈ C^{1,1}_L(ℝⁿ)` bounded below
with infimum `f* = fstar`, `μs > 0` (the paper's `µ`), and `f*_µ = fμstar` the infimum of the
Gaussian smoothing `f_µ` ((3.10); the paper writes `min`, which need not be attained, so the
infimum is used), every `x` satisfies `−µ²Ln ≤ [f_µ(x) − f*_µ] − [f(x) − f*] ≤ µ²Ln`. -/
theorem eq_3_11 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μs : ℝ) (hμs : 0 < μs) (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    (fμstar : ℝ) (hfμstar : IsGLB (Set.range (RandomGradFree.Shared.smoothing f μs)) fμstar) :
    ∀ x, -(μs ^ 2 * L * (n : ℝ)) ≤
        (RandomGradFree.Shared.smoothing f μs x - fμstar) - (f x - fstar) ∧
      (RandomGradFree.Shared.smoothing f μs x - fμstar) - (f x - fstar) ≤ μs ^ 2 * L * (n : ℝ) := by sorry

end GhadimiLan.RSGF
