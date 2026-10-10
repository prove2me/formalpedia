-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_af_strictly_continuous
-- name    : NonconvexDRS.ImageSmooth.af_strictly_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:32.740529+00:00
-- url     : https://prove2.me/theorems/1e9ca110-3a76-4006-9d90-7d19cbeec99c
-- title:
--   Proof of Theorem 5.13, p. 25 — for C¹ f, (Af) is real-valued, strictly continuous, with nonempty limiting subdifferential
-- statement:
--   Let $A\in\mathbb R^{p\times n}$ be surjective and $f:\mathbb R^n\to\mathbb R$ lower semicontinuous, and suppose there is $\beta\ge0$ such that $x\mapsto f(x)+\frac\beta2\|Ax-s\|^2$ is level bounded for every $s\in\mathbb R^p$. If moreover $f$ is continuously differentiable, then the image function $(Af)(s)=\inf\{f(x)\mid Ax=s\}$ is real-valued, strictly continuous (locally Lipschitz) on $\mathbb R^p$, and its limiting subdifferential $\partial(Af)(s)$ is nonempty at every $s\in\mathbb R^p$.
--
--   Nonemptiness of $\partial(Af)$ everywhere is the first hypothesis of the subdifferential characterization of smoothness (Lemma 2.1), through which Theorem 5.13 is proved.
--
--   **Formalization Note** The page justifies this step by "since $f$ is differentiable". Differentiability alone does not suffice: with $n=p=1$, $A=1$ and $f(x)=x^2\sin(1/x^2)+2x^2$ ($f(0)=0$), $f$ is differentiable, lower semicontinuous and level bounded, yet $(Af)=f$ is not locally Lipschitz at $0$. The statement therefore assumes $f\in C^1$, which holds in cases (ii) and (iii) of Theorem 5.13 ($f\in C^{1,1}$). The page's intermediate claim $\partial^\infty(Af)(s)\subseteq\ker A^\top=\{0\}$ about horizon subgradients is not formalized. The limiting subdifferential is the published `NonconvexSplitting.Shared.LimitingSubdiff`.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 25, proof of Theorem 5.13

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proof of Theorem 5.13, p. 25: under the hypotheses of Theorem 5.13 and for continuously
differentiable `f`, the image function `(Af)` is real-valued, strictly continuous (locally
Lipschitz) and has nonempty limiting subdifferential at every point of `ℝᵖ`. -/
theorem af_strictly_continuous {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hA : Function.Surjective A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LowerSemicontinuous f)
    (hlev : ∃ β : ℝ, 0 ≤ β ∧ ∀ s : EuclideanSpace ℝ (Fin p), ∀ α : ℝ,
      Bornology.IsBounded {x | f x + β / 2 * ‖A x - s‖ ^ 2 ≤ α})
    (hC1 : ContDiff ℝ 1 f) :
    ∃ F : EuclideanSpace ℝ (Fin p) → ℝ,
      (∀ s, imageFn A (fun x => (f x : EReal)) s = (F s : EReal)) ∧ LocallyLipschitz F ∧
      ∀ s, (LimitingSubdiff (imageFn A (fun x => (f x : EReal))) s).Nonempty := by sorry

end NonconvexDRS.ImageSmooth
