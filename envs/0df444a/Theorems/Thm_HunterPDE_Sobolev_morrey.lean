-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_morrey
-- name    : HunterPDE.Sobolev.morrey
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:23:03.848988+00:00
-- url     : https://prove2.me/theorems/5fbc452a-1a5d-4811-a2f1-c3f25ecba1d1
-- title:
--   Theorem 3.36 — Morrey's inequality for C_c^∞(ℝⁿ), p > n
-- statement:
--   Let $n < p < \infty$ and $\alpha = 1 - n/p$. There is a constant $C = C(n, p)$ such that for all $f \in C_c^\infty(\mathbb{R}^n)$
--   $$[f]_\alpha \le C\, \|Df\|_p \qquad (3.12)$$
--   $$\sup_{\mathbb{R}^n} |f| \le C\, \|f\|_{W^{1,p}} \qquad (3.13)$$
--   where $[\cdot]_\alpha$ is the Hölder seminorm $[\cdot]_{\alpha,\mathbb{R}^n}$ of (1.1), $|Df|$ is the Euclidean length of the gradient and $\|\cdot\|_{W^{1,p}}$ is the norm of Definition 3.23.
--
--   For $p > n$ a gradient in $L^p$ forces Hölder continuity with exponent $1 - n/p$ and boundedness; this is the basis of the embedding $W^{1,p}(\mathbb{R}^n) \hookrightarrow C^{0,\alpha}(\mathbb{R}^n)$ (Theorem 3.37).
--
--   **Formalization Note.** One constant serves both inequalities, which is equivalent to two constants (take the larger). It is chosen after $n, p$ and before $f$. (3.13) is stated pointwise, $|f(x)| \le C\|f\|_{W^{1,p}}$ for every $x$, which is equivalent to the bound on the supremum. The clause "with $\alpha = 1$ if $p = \infty$" of the printed statement is outside the stated range $n < p < \infty$ and is not formalized. Values are in $[0, \infty]$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 68, Theorem 3.36

import Mathlib
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Definitions.Def_HunterPDE_Shared_HolderSeminorm

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Theorem 3.36 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 68 (Morrey): let `n < p < ∞`
and `α = 1 − n/p`. There is a constant `C = C(n, p)` (chosen before `f`) such that for all
`f ∈ C_c^∞(ℝⁿ)`: `[f]_α ≤ C ‖Df‖_p` (3.12), with `[·]_α` the Hölder seminorm (1.1) on `ℝⁿ` and `|Df|`
the Euclidean gradient norm, and `sup_{ℝⁿ} |f| ≤ C ‖f‖_{W^{1,p}}` (3.13), stated pointwise. -/
theorem morrey {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        Shared.holderSeminorm (1 - (n : ℝ) / p) Set.univ f ≤
            (C : ENNReal) * eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume ∧
          ∀ x, ENNReal.ofReal |f x| ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by sorry

end HunterPDE.Sobolev
