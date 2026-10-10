-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_af_lsc_argmin
-- name    : NonconvexDRS.ImageSmooth.af_lsc_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:34.674554+00:00
-- url     : https://prove2.me/theorems/1f30e582-4d5d-4972-9055-c95e53c4e70c
-- title:
--   Proof of Theorem 5.13, p. 25 — (Af) is lsc and X(s) = argmin {f(x) | Ax = s} is nonempty for every s
-- statement:
--   Let $A\in\mathbb R^{p\times n}$ be surjective and $f:\mathbb R^n\to\mathbb R$ lower semicontinuous, and suppose there is $\beta\ge0$ such that for every $s\in\mathbb R^p$ the function $x\mapsto f(x)+\frac\beta2\|Ax-s\|^2$ is level bounded. Then:
--
--   1. the image function $(Af)(s)=\inf\{f(x)\mid Ax=s\}$ is lower semicontinuous on $\mathbb R^p$;
--   2. for every $s\in\mathbb R^p$ the set
--   $$X(s)=\operatorname*{arg\,min}_{x}\{f(x)\mid Ax=s\}$$
--   is nonempty.
--
--   These are the conclusions the proof of Theorem 5.13 draws from the parametric-minimization theorem [Rockafellar–Wets, Thm. 1.32]; they make $(Af)$ a lower semicontinuous, real-valued function attained on every fibre.
--
--   **Formalization Note** The level-boundedness hypothesis is stated with one $\beta\ge0$ for all $s$, as on the page. The page's further remark that $H(x,s)=f(x)+\delta_{\{0\}}(Ax-s)$ is uniformly level bounded is a tool of the proof and is not stated.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 25, proof of Theorem 5.13

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proof of Theorem 5.13, p. 25: under the hypotheses of Theorem 5.13 (`A` surjective, `f` lsc,
`f + (β/2)‖A · - s‖²` level bounded for all `s`, for one `β ≥ 0`), the image function `(Af)` is
lsc and `X(s) = argmin {f(x) | Ax = s}` is nonempty for every `s`. -/
theorem af_lsc_argmin {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α}) :
    LowerSemicontinuous (imageFn A (fun x => (f x : EReal))) ∧
      ∀ s, ∃ x, A x = s ∧ ∀ x', A x' = s → f x ≤ f x' := by sorry

end NonconvexDRS.ImageSmooth
